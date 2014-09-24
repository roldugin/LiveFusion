{-# LANGUAGE GADTs, PatternGuards, StandaloneDeriving #-}

-- | Loop is a representation of a DSL with basic blocks
--   and explicit control flow using goto's.
--
--   It can be used for things other than loops since there is
--   no fixed loop structure but probably shouldn't.
--
--   The language offers statements for direct array manipulation.

module Data.LiveFusion.Loop where

import Data.LiveFusion.Scalar.HOAS as HOAS
import qualified Data.LiveFusion.Scalar.Convert  as DeBruijn
import qualified Data.LiveFusion.Scalar.DeBruijn as DeBruijn
import Data.LiveFusion.Backend
import Data.LiveFusion.Util
import Data.LiveFusion.Types
import Data.LiveFusion.AliasMap ( AliasMap )
import qualified Data.LiveFusion.AliasMap as AMap

-- We should not be importing any backend specific stuff, but for now we hardcoded Exp to be depend on THElt
-- That is, elements that can be generated in TemplateHaskell
import Data.LiveFusion.HsBackend.Types

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Maybe

import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Dynamic
import Data.List as List
import Data.Monoid
import Control.Applicative ( (<|>), (<$>) )
import Control.Monad
import Control.Category ( (>>>) )


type Id = Int

type Name  = String

type Arg   = Dynamic



-- Variables
-- ----------------------------------------------------------------------------

data Var = IdVar Name Id
         | SimplVar Name
  deriving ( Eq, Ord )

instance Show Var where
  show = pprVar

var :: Name -> Id -> Var
var = IdVar

eltVar :: Id -> Var
eltVar = var "elt"

indexVar :: Id -> Var
indexVar = var "ix"

lengthVar :: Id -> Var
lengthVar = var "len"

arrayVar :: Id -> Var
arrayVar = var "arr"

resultVar :: Var
resultVar = SimplVar "result"

-- TODO These are all kinda hacky. We should use the Term language here.
ltFn = SimplVar "(<)"
plusFn = SimplVar "(+)"
lengthFn = SimplVar "arrayLength"
readFn = SimplVar "readArray"



-- Blocks
-------------------------------------------------------------------------------

data Block = Block [Stmt] (Maybe Stmt)


emptyBlock :: Block
emptyBlock = Block [] Nothing


blockStmts :: Block -> [Stmt]
blockStmts (Block stmts final) = stmts ++ maybeToList final


addStmtsToBlock :: [Stmt] -> Block -> Block
addStmtsToBlock stmts (Block stmts0 final0) = Block (stmts0 ++ stmts) final0


setBlockFinal :: Stmt -> Block -> Block
setBlockFinal final (Block stmts _) = Block stmts (Just final)


unsetBlockFinal :: Block -> Block
unsetBlockFinal (Block stmts _) = Block stmts Nothing


rewriteBlockLabels :: [Set Label] -> Block -> Block
rewriteBlockLabels lbls (Block stmts final) = Block stmts' final'
  where
    stmts' = map (rewriteStmtLabels lbls) stmts
    final' = rewriteStmtLabels lbls <$> final


-- Labels
-------------------------------------------------------------------------------

data Label = Label Name Id
  deriving ( Eq, Ord )

instance Show Label where
  show (Label nm i) = nm ++ "_" ++ show i



-- Statements
-------------------------------------------------------------------------------

data Stmt = Bind   Var Expr
          | Assign Var Expr
          | Case   Expr Label Label
          | Guard  Expr Label
          | Goto   Label
          | Return Expr
          -- Array statements.
          -- They are here because they are stateful operations.
          -- Perhaps there is a cleaner way to do this.
          | NewArray   Var  {- Array name -}
                       Expr {- Array length -}
          | ReadArray  Var  {- Variable to read into -}
                       Var  {- Array name -}
                       Expr {- Index -}
          | WriteArray Var  {- Array name -}
                       Expr {- Index -}
                       Expr {- Element -}
          | SliceArray Var  {- New array name (TODO: ugly) -}
                       Var  {- Array name -}
                       Expr {- Array length -}


bindStmt     = Bind
assignStmt   = Assign
caseStmt     = Case
guardStmt    = Guard
gotoStmt     = Goto
returnStmt   = Return
newArrStmt   = NewArray
readArrStmt  = ReadArray
writeArrStmt = WriteArray
sliceArrStmt = SliceArray


-- | In the final loop we choose just one label out of all
--   and use it everywhere where the same set of labels is used.
--
-- For example
-- @
-- body_3:
-- body_2:
--   elt_3 = f elt_2
--   goto yield_3
-- @
-- gets rewritten to use the smallest label
-- @
-- body_3:
-- body_2:
--   elt_3 = f elt_2
--   goto yield_2    <-- changed
-- @


rewriteStmtLabels :: [Set Label] -> Stmt -> Stmt
rewriteStmtLabels lbls = go
  where
    rw l = theSynonymLabel lbls l

    go (Case v l1 l2) = Case v (rw l1) (rw l2)
    go (Guard v l)    = Guard v (rw l)
    go (Goto l)       = Goto (rw l)
    go _stmt          = _stmt

-- Loops
-------------------------------------------------------------------------------

data Loop = Loop { -- | Loop entry block
                   loopEntry        :: Maybe Label

                   -- | Global arguments and their values
                 , loopArgs         :: (Map Var Arg)

                   -- | Resulting manifest array
                 , loopArrResult    :: Maybe Id  -- May not be the best way to represent this,
                                                 -- but currently the easiest

                   -- | Resulting scalar result
                 , loopScalarResult :: Maybe Var

                   -- | Loops's code block with their accosiated labels
                 , loopBlockMap     :: BlockMap
                 }


-- | A collection of statement blocks identified by labels akin to ASM labels.
--
--   Each block can be identified by multiple labels. A new synonym label can
--   be added using 'AliasMap.addSynonym'.
--
--   In the following example the block is both labelled 'init_0' and 'init_1'.
-- @
--   init_0:
--   init_1:
--     let x = 42
--     let y = 1984
-- @
type BlockMap = AliasMap Label Block


-- | Reduces a set of labels to one specific label.
--
--   The reduction function can be anything as long as the loop doesn't change
--   after we start reducing all label synonyms to one concrete label.
theOneLabel :: Set Label -> Label
theOneLabel = Set.findMin 


-- | Rewrites one label to its synonym from the loop following a predefined
--   convention.
theSynonymLabel :: [Set Label] -> Label -> Label
theSynonymLabel lbls l = theOneLabel $ synonyms
  where
    synonyms = fromMaybe err
             $ find (l `Set.member`) lbls
    err = error "theSynonymLabel: label not found in sets"


addSynonymLabel :: Label -> Label -> Loop -> Loop
addSynonymLabel nu old loop
  = loop { loopBlockMap = AMap.addSynonym nu old (loopBlockMap loop) }


loopBlocks :: Loop -> [Block]
loopBlocks = AMap.elems . loopBlockMap


updateBlock :: Label -> (Block -> Block) -> Loop -> Loop
updateBlock lbl f loop = putBlock lbl block' loop
  where
    block  = getBlock lbl loop
    block' = f block


-- | Retreives an existing block out of the loop or returns and empty block
getBlock :: Label -> Loop -> Block
getBlock lbl loop = fromMaybe emptyBlock maybeBlock
  where
    maybeBlock = AMap.lookup lbl (loopBlockMap loop)


putBlock :: Label -> Block -> Loop -> Loop
putBlock lbl blk loop = loop { loopBlockMap = loopBlockMap' }
  where
    loopBlockMap' = AMap.insert lbl blk (loopBlockMap loop)


-- | Append a statement to the specified code block.
addStmt :: Stmt -> Label -> Loop -> Loop
addStmt stmt lbl = updateBlock lbl (addStmtsToBlock [stmt])


-- | Append multiple statements to the specified code block.
addStmts :: [Stmt] -> Label -> Loop -> Loop
addStmts stmts lbl = updateBlock lbl (addStmtsToBlock stmts)


-- | Replace all statements (including final) in a block with the specified ones.
replaceStmts :: [Stmt] -> Label -> Loop -> Loop
replaceStmts stmts lbl = updateBlock lbl (const $ addStmtsToBlock stmts emptyBlock)


setLoopEntry :: Label -> Loop -> Loop
setLoopEntry lbl loop = loop { loopEntry = Just lbl }


unsafeLoopEntry :: Loop -> Label
unsafeLoopEntry = fromMaybe noEntryErr . loopEntry
  where
    noEntryErr = error "exendedEnv: loop entry must be specified"


-- | Sets the final statement of a given block to be goto to another block
setFinalGoto :: Label -> Label -> Loop -> Loop
setFinalGoto from to = updateBlock from 
                                   (setBlockFinal $ gotoStmt to)


-- Scalar and Array results manipulation
--------------------------------------------------------------------------------

setArrResultImpl :: Maybe Id -> Loop -> Loop
setArrResultImpl mbId loop = loop { loopArrResult = mbId }


setArrResult :: Id -> Loop -> Loop
setArrResult i = setArrResultImpl (Just i)


unsetArrResult :: Loop -> Loop
unsetArrResult = setArrResultImpl Nothing


setScalarResultImpl :: Maybe Var -> Loop -> Loop
setScalarResultImpl mbVar loop = loop { loopScalarResult = mbVar }


setScalarResult :: Var -> Loop -> Loop
setScalarResult v = setScalarResultImpl (Just v)


unsetScalarResult :: Loop -> Loop
unsetScalarResult = setScalarResultImpl Nothing


-- | Unsets scalar result along the way.
setArrResultOnly :: Id -> Loop -> Loop
setArrResultOnly i = unsetScalarResult
                   . setArrResult i



-- * Pretty printing
--------------------------------------------------------------------------------

pprBlockMap :: BlockMap -> String
pprBlockMap = unlines . map pprOne . sortOnKeysBy cmp . AMap.assocs
  where
    pprOne (lbls, blk) = (pprLabels lbls) ++
                         (indent 1 $ pprBlock blk)

    pprLabels = unlines . map (\l -> pprLabel l ++ ":") . Set.toList

    cmp :: Set Label -> Set Label -> Ordering
    cmp s1 s2 = let Label nm1 id1 = theOneLabel s1
                    Label nm2 id2 = theOneLabel s2
                in  compare id1 id2 `thenCmp` fixedCompare stdLabelNames nm1 nm2


pprBlock :: Block -> String
pprBlock (Block stmts mbfinal)
  = unlines $ map pprStmt (stmts ++ fin)
  where fin = maybe [] return mbfinal -- returns either singleton or empty list


pprStmt :: Stmt -> String
pprStmt (Bind v e)     = "let" +-+ pprVar v +-+ "=" +-+ pprExpr e
pprStmt (Assign v e)   = pprVar v +-+ ":=" +-+ pprExpr e
pprStmt (Guard p l)    = "unless" +-+ pprExpr p +-+ "|" +-+ pprLabel l
pprStmt (Case p l1 l2) = "if" +-+ pprExpr p +-+ "|" +-+ pprLabel l1 +-+ pprLabel l2
pprStmt (Goto l)       = "goto" +-+ pprLabel l
pprStmt (NewArray arr n)        = "let" +-+ pprVar arr +-+ "= newArray" +-+ pprExpr n
pprStmt (ReadArray x arr i)     = "let" +-+ pprVar x +-+ "= readArray" +-+ pprVar arr +-+ pprExpr i
pprStmt (WriteArray arr i x)    = "writeArray" +-+ pprVar arr +-+ pprExpr i +-+ pprExpr x
pprStmt (SliceArray arr' arr n) = "let" +-+ pprVar arr' +-+ "= sliceArray" +-+ pprVar arr +-+ pprExpr n
pprStmt (Return e)     = "return" +-+ pprExpr e
pprStmt _              = "pprStmt: Unknown Statement"


pprLabel :: Label -> String
pprLabel = show


instance Show Loop where
  show (Loop loopEntry loopArgs loopArrResult loopScalarResult loopBlockMap)
    = "Loop Entry:    "  ++  maybe "None" pprLabel loopEntry                   ++\
      "Loop Args:     "  ++  (show $ Map.keys loopArgs)                        ++\
      "Array Result:  "  ++  maybe "None" (pprVar . arrayVar) loopArrResult    ++\
      "Scalar Result: "  ++  maybe "None" pprVar              loopScalarResult ++\
      "BlockMap:      "  ++\ pprBlockMap loopBlockMap


pprVarMap :: VarMap -> String
pprVarMap = ("Transitive Variable Map:" ++\)
          . unlines . map pprVarMapEntry . Map.assocs
  where
    pprVarMapEntry (lbl,vars) = pprLabel lbl ++ ": " ++ show vars



--------------------------------------------------------------------------------


addArg var arg loop = loop { loopArgs = loopArgs' }
  where loopArgs' = Map.insert var arg (loopArgs loop)


-- * Several predefined labels
--------------------------------------------------------------------------------

initNm, guardNm, bodyNm, yieldNm, bottomNm, doneNm :: Name
initNm   = "init"
guardNm  = "guard"
bodyNm   = "body"
yieldNm  = "yield"
bottomNm = "bottom"
doneNm   = "done"


initLbl, guardLbl, bodyLbl, yieldLbl, bottomLbl, doneLbl :: Id -> Label
initLbl   = Label initNm
guardLbl  = Label guardNm
bodyLbl   = Label bodyNm
yieldLbl  = Label yieldNm
bottomLbl = Label bottomNm
doneLbl   = Label doneNm


-- | A list of standard label constructors
stdLabelNames :: [Name]
stdLabelNames = [initNm, guardNm, bodyNm, yieldNm, bottomNm, doneNm]


-- | Add synonym labels for the basic predefined labels (init, guard, etc..)
addDefaultSynonymLabels :: Id -> Id -> Loop -> Loop
addDefaultSynonymLabels nu old loop
  = foldl alias loop [initLbl, guardLbl, bodyLbl, yieldLbl, bottomLbl, doneLbl]
  where
    alias loop lblMaker = addSynonymLabel (lblMaker nu) (lblMaker old) loop


-- | Add control flow between some of the known blocks
addDefaultControlFlow :: Id -> Loop -> Loop
addDefaultControlFlow uq loop
  = foldl addFinalGoto loop
  $ [ (initLbl   , guardLbl)  -- Init   -> Guard
    , (guardLbl  , bodyLbl)   -- Guard  -> Body
    , (bodyLbl   , yieldLbl)  -- Body   -> Yield
    , (yieldLbl  , bottomLbl) -- Yield  -> Bottom
    , (bottomLbl , guardLbl)  -- Bottom -> Guard
    ]
  where
    addFinalGoto loop (from,to)
      = let fromLbl = from uq
            toLbl = to uq
        in  updateBlock fromLbl
                        (setBlockFinal $ gotoStmt toLbl)
                        loop


-- | Make sure all default blocks exist before we start adding synonyms.
--
--   This would usually happen in fresh loop. But for now we do it in pure
--   generators and nested combinators.
--
--   TODO: should probably not be necessary
touchDefaultBlocks :: Id -> Loop -> Loop
touchDefaultBlocks uq loop
  = foldl touch loop [initLbl, guardLbl, bodyLbl, yieldLbl, bodyLbl, doneLbl]
  where
    touch loop mkLbl = updateBlock (mkLbl uq) id {-do nothing-} loop


--------------------------------------------------------------------------------


-- * Environment
--------------------------------------------------------------------------------

-- | Per block environment which tracks the variables that the block
--   relies upon being present, the variables declared in this block as well as
--   variables that have been destructively assigned to in this block.
--
--   The environment can be used to compute the arguments to the block when presenting
--   it as pure function as well as detect programming errors of the DSL program.
--
data Env = Env { -- | Variables expected to be in environment
                 envAssumptions :: [Var]

                 -- | Newly declared variables
               , envDeclarations :: [Var]

                 -- | Variables that have been assigned to
               , envDirty :: [Var]

                 -- | LoopBlockMap to which control flow may be transferred
               , envNextBlocks :: [Label]
               }


err_DECLARED = "[Loop DSL Error] Variable already declared in the environment: "
err_NOTDECLARED = "[Loop DSL Error] Attempt to assign to a variable that is not in scope: "
-- Maximum one assignment per block for now (TODO)
err_ASSIGNED = "[Loop DSL Error] Variable already assigned to in this block: "


emptyEnv = Env [] [] [] []


declare :: Var -> Env -> Env
declare v env
  | (v `elem` envAssumptions env) || (v `elem` envDeclarations env) -- already declared
  = error (err_DECLARED ++ pprVar v)

  | otherwise
  = env { envDeclarations = v : envDeclarations env }


markEnvDirty :: Var -> Env -> Env
markEnvDirty v env
  | (v `notElem` envAssumptions env) && (v `notElem` envDeclarations env)
  = error (err_NOTDECLARED ++ pprVar v)

  | (v `elem` envDirty env)
  = error (err_ASSIGNED ++ pprVar v)

  | otherwise
  = env { envDirty = v : envDirty env }


assume :: Var -> Env -> Env
assume v env
  | (v `elem` envDeclarations env) || (v `elem` envAssumptions env) -- already assumed (or declared)
  = env

  | otherwise
  = env { envAssumptions = v : envAssumptions env }


assumeMany :: [Var] -> Env -> Env
assumeMany vars env = foldr assume env vars


-- | Lists the block as as potential next block to which control flow will be transferred
adoptBlock :: Label -> Env -> Env
adoptBlock lbl env
  = env { envNextBlocks = [lbl] `union` envNextBlocks env }


-- | Retrieves the free variables of an expression
varsE :: Expr -> [Var]
varsE (VarE v)   = [v]
varsE (AppE f x) = varsE f ++ varsE x
varsE (TermE _)  = [] -- DeBruijn Terms are closed
varsE (LitE _)   = [] -- Literals are constant terms


-- | Compute Environment for a block
--
-- Loops for:
-- + New variable declarations (declare)
-- + Variables assumed to be in scope (assume/assumeAllIn)
-- + Other blocks to which it is possible to jump from this block (adoptBlock)
-- + Variable mutations/updates (markEnvDirty)
--
-- Call to declare should come last to be more sure nothings is declared more than once.
blockEnv :: Block -> Env
blockEnv blk = foldl (flip analyse) emptyEnv (blockStmts blk)
  where
    analyse :: Stmt -> Env -> Env
    analyse (Bind v e)     = assumeAllIn e >>> declare v
    analyse (Assign v e)   = assumeAllIn e >>> markEnvDirty v
    analyse (Case p lt lf) = assumeAllIn p >>> adoptBlock lt >>> adoptBlock lf
    analyse (Guard p lf)   = assumeAllIn p >>> adoptBlock lf
    analyse (Goto l)       = adoptBlock l
    analyse (NewArray arr n)        = assumeAllIn n >>> declare arr
    analyse (ReadArray x arr i)     = assume arr >>> assumeAllIn i >>> declare x
    analyse (WriteArray arr i x)    = assume arr >>> assumeAllIn i >>> assumeAllIn x
    analyse (SliceArray arr' arr n) = assume arr >>> assumeAllIn n >>> declare arr'
    analyse (Return v)     = assumeAllIn v

    assumeAllIn = assumeMany . varsE


-- | Transitive environment assumptions
--
--   That is, all of the variables that will be required by the block with the
--   given label as well as any other block to where the control may end up.
--
--   This does not include variables that are bound by this of the future blocks.
--   These are conceptually all the free variables of the block and its futures.
type VarMap = Map Label [Var]


-- | A simpler replacement of liveness analysis. Computes a maximal set of variables
--   that may be required by the block and its futures.
--
--   The liveness analysis as such only applies to variables that are never used outside
--   the block they are declared in.
extendedEnv :: Loop -> VarMap
extendedEnv loop = purgeBlockLocalVars
                 $ traceEnv allLoopArgVars -- all declarations so far
                            Map.empty
                            (unsafeLoopEntry loop)
  where
    allLoopArgVars     = Map.keys $ loopArgs loop
    allLoopDecls       = concatMap (envDeclarations . blockEnv) (loopBlocks loop)
    allLoopAssumptions = concatMap (envAssumptions  . blockEnv) (loopBlocks loop)
    allBlockLocalVars  = (allLoopDecls `union` allLoopArgVars)
                       \\ allLoopAssumptions

    purgeBlockLocalVars :: VarMap -> VarMap
    purgeBlockLocalVars = Map.map (\\ allBlockLocalVars)

    traceEnv :: [Var] -> VarMap -> Label -> VarMap
    traceEnv pastDecls emap currLbl
      | currLbl `Map.member` emap  -- Cycle detected - stop
      = emap

      | otherwise
      = let assms = envAssumptions env  -- environment assumptions of current block

            partialMap = Map.insert currLbl pastDecls emap -- insert all available declarations
                                                           -- as requirements for this block

            env        = blockEnv (getBlock currLbl loop)  -- this block's environment

            partialDecls = pastDecls ++ envDeclarations env  -- all known declarations
                                                             -- including this block's ones

            nextLbls   = envNextBlocks env   -- all possible next blocks

            -- Merge environments of past and future blocks.
            -- NOTE: If a block pops up multiple times it means there are multiple paths to
            --       it in the control flow graph. Use only those declarations that all
            --       paths can provide.
            resultMap = foldl (Map.unionWith List.intersect)
                        partialMap                 -- extended environment of this and past blocks
                      $ map (traceEnv partialDecls partialMap)  -- assumptions of future blocks
                      $ nextLbls

        in  resultMap


--------------------------------------------------------------------------------


-- | Reduces the minimal set of labels
postprocessLoop :: Loop -> Loop
postprocessLoop = rewriteLoopLabels
                . reorderDecls
                . insertResultArray


rewriteLoopLabels :: Loop -> Loop
rewriteLoopLabels loop
  = loop { loopBlockMap = newBlockMap
         , loopEntry    = newEntry }
  where
    lbls = AMap.keys $ loopBlockMap loop
    newEntry = theSynonymLabel lbls <$> loopEntry loop
    newBlockMap = AMap.map (rewriteBlockLabels lbls) (loopBlockMap loop)


insertResultArray :: Loop -> Loop
insertResultArray loop
  | Just uq <- loopArrResult loop
  = let alloc = newArrStmt arr (varE bound)
        write = writeArrStmt arr (varE ix) (varE elt)
        slice = sliceArrStmt resultVar arr (varE ix)
        ret   = returnStmt (varE resultVar)

        arr   = arrayVar  uq
        bound = lengthVar uq
        ix    = indexVar  uq
        elt   = eltVar    uq

        process = addStmt alloc (initLbl uq)
              >>> addStmt write (yieldLbl uq)
              >>> addStmt slice (doneLbl uq)
              >>> addStmt ret   (doneLbl uq)

    in  process loop


-- | All declarations must go first in the block.
--
--   Otherwise, some of them may not even be in scope when they are required.
--   E.g. when a jump on a guard occurs.
--
--   TODO: Explain this better, sketchy explanation follows.
--         This happens because a block is aggregated from statements coming
--         from different places. So declarations and control flow are interleaved.
--         However, as soon as control flow occurs it may need all of the variables
--         known to the block. This won't be possible if the declaration comes after
--         the control transfer.
reorderDecls :: Loop -> Loop
reorderDecls loop = loop { loopBlockMap = AMap.map perblock (loopBlockMap loop) }
  where
    perblock (Block stmts final) = Block (reorder stmts) final

    reorder = uncurry (++)
            . partition isDecl

    isDecl (Bind   _ _)      = True
    isDecl (Assign _ _)      = True
    isDecl (ReadArray _ _ _) = True
    isDecl _            = False

instance Monoid Loop where
  mempty = Loop Nothing Map.empty Nothing Nothing AMap.empty
  mappend loop1 loop2
    = Loop { loopEntry        = loopEntry    `joinWith` (<|>)
           , loopArgs         = loopArgs     `joinWith` Map.union
           , loopArrResult    = Nothing
           , loopScalarResult = Nothing
           , loopBlockMap     = loopBlockMap `joinWith` AMap.unionWith appendLoopBlockMap
           }
    where
      joinWith :: (Loop  -> field)          -- field to take from loop
               -> (field -> field -> field) -- joining function
               -> field                    -- new field
      field `joinWith` f = f (field loop1) (field loop2)


append :: Loop -> Loop -> Loop
append = mappend


empty :: Loop
empty = mempty


appendLoopBlockMap :: Block -> Block -> Block
appendLoopBlockMap (Block stmts1 final1) (Block stmts2 final2)
  = Block (stmts1 ++ stmts2) (final1 <|> final2)


-- | Represents an expression in the loop.
--
--   NOTE: It would be difficult to type the expression tree as `Expr a'
--         as we would no longer be able to easily construct collections
--         of such expressions, e.g.:
--   > [Expr Int, Expr Double, Expr Double]
--
--   Thoughts:
--   1. One way to keep the types would be to keep a TypeRep inside each Var.
--
--   2. Alternatively we could minimise the use of data structures such as lists
--   and maps and instead keep more stuff in the tree itself.
--
--   3. Now that we have DeBruijn term language that we use for scalar
--      functions specified by the user, perhaps we do not need a separate Expr
--      language.
--
data Expr where
  VarE  :: Var                              -> Expr
  AppE  :: Expr -> Expr                     -> Expr
  TermE :: (Typeable t) => HOAS.Term t      -> Expr
  LitE  :: (THElt e, Elt e) => e            -> Expr

instance Show Expr where
  show = pprExpr


vAppE :: Var -> Var -> Expr
vAppE f x = AppE (varE f) (varE x)


varE :: Var -> Expr
varE = VarE


constE :: (THElt e, Elt e) => e -> Expr
constE = LitE


pprExpr :: Expr -> String
pprExpr (VarE v)
  = pprVar v
pprExpr (AppE f x)
  = (pprExpr f) `space` (pprExpr x)
pprExpr (TermE t)
  -- TODO: Convert should not be here.
  = paren $ DeBruijn.pprTerm $ DeBruijn.convert t
pprExpr (LitE i)
  = show i


pprName :: Name -> String
pprName = id


pprVar :: Var -> String
pprVar (IdVar name ident) = pprName name ++ "_" ++ pprId ident
pprVar (SimplVar name) = pprName name

pprId :: Id -> String
pprId = show
