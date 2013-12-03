{-# LANGUAGE GADTs, PatternGuards #-}

-- | Loop is an abstract representation of a loop computation.
--   It can be used to generate loop code.

module Data.LiveFusion.Loop where

import Data.LiveFusion.Util
import Data.LiveFusion.AliasMap ( AliasMap )
import qualified Data.LiveFusion.AliasMap as AMap

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

ltFn = SimplVar "(<)"
plusFn = SimplVar "(+)"
lengthFn = SimplVar "lengthArray"
readFn = SimplVar "readArray"



-- Blocks
-------------------------------------------------------------------------------

data Block = Block [Stmt] (Maybe Stmt)


emptyBlock :: Block
emptyBlock = Block [] Nothing


blockStmts :: Block -> [Stmt]
blockStmts (Block stmts _final) = stmts


blockFinal :: Block -> Maybe Stmt
blockFinal (Block _stmts final) = final


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

data Stmt = Bind Var Expr
          | Assign Var Expr
          | Case Var Label Label
          | Guard Var Label
          | Goto Label
          -- Array statements.
          -- They are here because they are stateful operations.
          -- Perhaps there is a cleaner way to do this.
          | NewArray Var {- Array name -}
                     Var {- Array length -}
          | WriteArray Var {- Array name -}
                       Var {- Index -}
                       Var {- Element -}
          | SliceArray Var {- New array name (TODO: ugly) -}
                       Var {- Array name -}
                       Var {- Array length -}
          | Return Var


bindStmt     = Bind
assignStmt   = Assign
caseStmt     = Case
guardStmt    = Guard
gotoStmt     = Goto
newArrStmt   = NewArray
writeArrStmt = WriteArray
sliceArrStmt = SliceArray
returnStmt   = Return


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


-- | A collection of statememt blocks identified by labels akin to asm labels.
--
--   Each block can be identified by multiple labels. A new synonym label can
--   be added useing 'AliasMap.addSynonym'.
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


-- Append a statement to the specified code block
addStmt :: Stmt -> Label -> Loop -> Loop
addStmt stmt lbl = updateBlock lbl (addStmtsToBlock [stmt])


addStmts :: [Stmt] -> Label -> Loop -> Loop
addStmts stmts lbl = updateBlock lbl (addStmtsToBlock stmts)


setLoopEntry :: Label -> Loop -> Loop
setLoopEntry lbl loop = loop { loopEntry = Just lbl }


unsafeLoopEntry :: Loop -> Label
unsafeLoopEntry = fromMaybe noEntryErr . loopEntry
  where
    noEntryErr = error "exendedEnv: loop entry must be specified"


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



-- Pretty printing
--------------------------------------------------------------------------------

pprBlockMap :: BlockMap -> String
pprBlockMap = unlines . map pprOne . AMap.assocs
  where
    pprOne (lbls, blk) = (pprLabels lbls) ++\
                         (indent 1 $ pprBlock blk)
    pprLabels = unlines . map (\l -> pprLabel l ++ ":") . Set.toList


pprBlock :: Block -> String
pprBlock (Block stmts mbfinal)
  = unlines $ map pprStmt (stmts ++ fin)
  where fin = maybe [] return mbfinal -- returns either singleton or empty list


pprStmt :: Stmt -> String
pprStmt (Bind v e)     = "let " ++ pprVar v ++ " = " ++ pprExpr e
pprStmt (Assign v e)   = pprVar v ++ " := " ++ pprExpr e
pprStmt (Guard v l)    = "guard on " ++ pprVar v ++ " | onFail: " ++ pprLabel l
pprStmt (Case p l1 l2) = "if " ++ pprVar p ++
                         " then " ++ pprLabel l1 ++
                         " else " ++ pprLabel l2
pprStmt (Goto l)       = "goto " ++ pprLabel l
pprStmt (NewArray arr n)        = pprVar arr ++ " = newArray " ++ pprVar n
pprStmt (WriteArray arr i x)    = pprVar arr ++ "[" ++ pprVar i ++ "] := " ++ pprVar x
pprStmt (SliceArray arr' arr n) = pprVar arr' ++ " = sliceArray " ++ pprVar arr ++ " " ++ pprVar n
pprStmt (Return v)     = "return " ++ pprVar v
pprStmt _              = "Unknown Stmt"

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


-- Several predefined labels
--------------------------------------------------------------------------------

initLbl, guardLbl, bodyLbl, writeLbl, bottomLbl, doneLbl :: Id -> Label
initLbl   = Label "init"
guardLbl  = Label "guard"
bodyLbl   = Label "body"
writeLbl  = Label "write"
bottomLbl = Label "bottom"
doneLbl   = Label "done"

-- | Add synonym labels for the basic predefined labels (init, guard, etc..)
addDefaultSynonymLabels :: Id -> Id -> Loop -> Loop
addDefaultSynonymLabels nu old loop
  = foldl alias loop [initLbl, guardLbl, bodyLbl, writeLbl, bottomLbl, doneLbl]
  where
    alias loop lblMaker = addSynonymLabel (lblMaker nu) (lblMaker old) loop

-- | Add control flow between some of the known blocks
addDefaultControlFlow :: Id -> Loop -> Loop
addDefaultControlFlow uq loop
  = foldl addFinalGoto loop
  $ [ (initLbl   , guardLbl)  -- Init   -> Guard
    , (guardLbl  , bodyLbl)   -- Guard  -> Body
    , (bodyLbl   , writeLbl)  -- Body   -> Write
    , (writeLbl  , bottomLbl) -- Body   -> Write
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
--   TODO: should probably not be neccessary
touchDefaultBlocks :: Id -> Loop -> Loop
touchDefaultBlocks uq loop
  = foldl touch loop [initLbl, guardLbl, bodyLbl, writeLbl, bodyLbl, doneLbl]
  where
    touch loop mkLbl = updateBlock (mkLbl uq) id {-do nothing-} loop


--------------------------------------------------------------------------------


-- Environment
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
err_NOTDECLARED = "[Loop DSL Error] Attmpt to assign to a variable that is not in scope: "
-- Maximum one assignment per block for now (TODO)
err_ASSIGNED = "[Loop DSL Error] Variable already assigned to in this block: "

{-
instance Monoid Env where
  mempty = Env [] [] []
  mappend (Env ass1 decl1 envDirty1) (Env ass2 decl2 envDirty2) = Env ass decl envDirty
    where
      ass   = (ass1 \\ decl) `List.union` (ass2 \\ decl) -- TODO: Ugly. Forcibly disjoins vars
                                                         -- assumed from prev loopBlockMap and
                                                         -- declared in the current block
      decl  = if null bad@(common [decl1, decl2, ass1, ass2])
                 then decl1 ++ decl2
                 else die err_DECLARED bad
      envDirty = disjointCheck err_ASSIGNED envDirty1 envDirty2 -- TODO: probably also wanna check the var
                                                       -- has been declared
      disjointCheck errString xs ys
            = let badVars = xs `intersect` ys
              in  if List.null badVars
                     then xs ++ ys
                     else die errString badVars
                          -- This is a crude way to fail, however there is no easy
                          -- static way to check this. Besides, the DSL is internal
                          -- to the library so it should not fail if everything is
                          -- implemented right.
      die errString badVars = error $ errString ++ show badVars
-}


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


-- | Lists the block as as potentian next block to which control flow will be transferred
adoptBlock :: Label -> Env -> Env
adoptBlock lbl env
  = env { envNextBlocks = [lbl] `union` envNextBlocks env }


-- | Retrieves the free variables of an expression
varsE :: Expr -> [Var]
varsE (VarE v) = [v]
varsE (App1 f v) = [f, v]
varsE (App2 f v1 v2) = [f, v1, v2]
varsE (App3 f v1 v2 v3) = [f, v1, v2, v3]
varsE (IntLit _) = []


blockEnv :: Block -> Env
blockEnv blk = foldl (flip analyse) emptyEnv (blockStmts blk)
  where
    analyse :: Stmt -> Env -> Env
    analyse (Bind v e)     = assumeMany (varsE e) >>> declare v
    analyse (Assign v e)   = assumeMany (varsE e) >>> markEnvDirty v
    analyse (Case v lt lf) = assume v >>> adoptBlock lt >>> adoptBlock lf
    analyse (Guard p lf)   = assume p >>> adoptBlock lf
    analyse (Goto l)       = adoptBlock l
    analyse (NewArray arr n)        = assume n >>> declare arr
    analyse (WriteArray arr i x)    = assumeMany [arr, i, x]
    analyse (SliceArray arr' arr n) = assume arr >>> assume n >>> declare arr'
    analyse (Return v)     = assume v


-- | Transitive environment assumptions
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


{-
insertControlFlow :: Loop -> Loop
insertControlFlow
  = addStmt (gotoStmt guardLbl)  initLbl    -- Init -> Guard
  . addStmt (gotoStmt bodyLbl)   guardLbl   -- Guard -> Body
  . addStmt (gotoStmt writeLbl) bodyLbl     -- Body -> Write
  . addStmt (gotoStmt bottomLbl) writeLbl    -- Body -> Write
  . addStmt (gotoStmt guardLbl)  bottomLbl  -- Bottom -> Guard
-}

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
  = let alloc = newArrStmt arr bound
        write = writeArrStmt arr ix elt
        slice = sliceArrStmt resultVar arr ix
        ret   = returnStmt resultVar

        arr   = arrayVar  uq
        bound = lengthVar uq
        ix    = indexVar  uq
        elt   = eltVar    uq

        process = addStmt alloc (initLbl uq)
              >>> addStmt write (writeLbl uq)
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
--         from different places. So decalarations and control flow are interleaved.
--         However, as soon as control flow occurs it may need all of the variables
--         known to the block. This won't be possible if the declaration comes after
--         the control transfer.
reorderDecls :: Loop -> Loop
reorderDecls loop = loop { loopBlockMap = AMap.map perblock (loopBlockMap loop) }
  where
    perblock (Block stmts final) = Block (reorder stmts) final

    reorder = uncurry (++)
            . partition isDecl

    isDecl (Bind   _ _) = True
    isDecl (Assign _ _) = True
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
data Expr where
  VarE   :: Var -> Expr
  App1   :: Var -> Var -> Expr
  App2   :: Var -> Var -> Var -> Expr
  App3   :: Var -> Var -> Var -> Var -> Expr
  IntLit :: Int -> Expr
  deriving ( Show, Eq )


pprExpr :: Expr -> String
pprExpr (VarE v)
  = pprVar v
pprExpr (App1 f x)
  = pprVar f `space` pprVar x
pprExpr (App2 f x y)
  = pprVar f `space` pprVar x `space` pprVar y
pprExpr (App3 f x y z)
  = pprVar f `space` pprVar x `space`
    pprVar y `space` pprVar z
pprExpr (IntLit i)
  = show i


pprName :: Name -> String
pprName = id


pprVar :: Var -> String
pprVar (IdVar name ident) = pprName name ++ "_" ++ pprId ident
pprVar (SimplVar name) = pprName name

pprId :: Id -> String
pprId = show

-- | Create a new variable from a the given one
--prime :: Var -> Var
--prime (Var name ident) = Var $ name ++ "'"