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
import Data.LiveFusion.DisjointSet as Rates
import qualified Data.LiveFusion.AliasMap as AMap


-- We should not be importing any backend specific stuff, but for now we hardcoded Exp to be depend on THElt
-- That is, elements that can be generated in TemplateHaskell
import Data.LiveFusion.HsBackend.Types
import Data.LiveFusion.HsBackend.Prelude

import Data.Maybe
import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Dynamic
import Data.List as List
import Data.Monoid
import Control.Applicative ( (<|>), (<$>) )
import Control.Monad
import Control.Category ( (>>>) )


type Id = Unique

type Name  = String

type Arg   = Dynamic


-------------------------------------------------------------------------------
-- * Variables

data Var = IdVar Name Id
         | SimplVar Name
  deriving ( Eq, Ord )

instance Show Var where
  show = pprVar


var :: Name -> Id -> Var
var = IdVar

eltVar :: Id -> Var
eltVar = var eltPrefix

indexVar :: Id -> Var
indexVar = var indexPrefix

lengthVar :: Id -> Var
lengthVar = var lengthPrefix

arrayVar :: Id -> Var
arrayVar = var arrayPrefix

resultVar :: Var
resultVar = SimplVar resultPrefix


eltPrefix    = "elt"
indexPrefix  = "ix"
lengthPrefix = "len"
arrayPrefix  = "arr"
resultPrefix = "result"


-- For easier language tree traversal
class Construct c where
  mapVars :: (Var -> Var) -> c -> c


-------------------------------------------------------------------------------
-- * Helper functions

-- This can go as soon as we make internal scalar language fully typed
plusInt :: Term Int -> Term Int -> Term Int
plusInt = plusTerm


ltInt :: Term Int -> Term Int -> Term Bool
ltInt = ltTerm


incStmt :: Var -> Stmt
incStmt v = assignStmt v incExpr
  where
    incExpr  = plusIntE `AppE` vE `AppE` oneE
    plusIntE = TermE (lam2 plusInt)
    vE       = varE v

zeroE, oneE :: Expr
zeroE = TermE (0 :: Term Int)
oneE  = TermE (1 :: Term Int)

-------------------------------------------------------------------------------
-- * Blocks

data Block = Block [Stmt] (Maybe Stmt)


emptyBlock :: Block
emptyBlock = Block [] Nothing


blockStmts :: Block -> [Stmt]
blockStmts (Block stmts final) = stmts ++ maybeToList final


addStmtsToBlock :: [Stmt] -> Block -> Block
addStmtsToBlock stmts (Block stmts0 final0) = Block (stmts0 ++ stmts) final0


-- | Replace all statements in the block.
--
-- Note that this keeps the final statement intact.
setStmtsOfBlock :: [Stmt] -> Block -> Block
setStmtsOfBlock stmts (Block _ final0) = Block stmts final0


setBlockFinal :: Stmt -> Block -> Block
setBlockFinal final (Block stmts _) = Block stmts (Just final)


unsetBlockFinal :: Block -> Block
unsetBlockFinal (Block stmts _) = Block stmts Nothing


rewriteBlockLabelsAndRates :: [Set Label] -> IntDisjointSet -> Block -> Block
rewriteBlockLabelsAndRates lbls rates (Block stmts final) = Block stmts' final'
  where
    stmts' = map (rewriteStmtRates rates)
           $ map (rewriteStmtLabels lbls)
           $ stmts
    final' = rewriteStmtRates rates
         <$> rewriteStmtLabels lbls
         <$> final


-------------------------------------------------------------------------------
-- * Labels

data Label = Label Name Id
  deriving ( Eq, Ord )

instance Show Label where
  show (Label nm i) = nm ++ "_" ++ show i


-------------------------------------------------------------------------------
-- * Statements

data Stmt = Bind   Var Expr
          | Assign Var Expr
          | Case   Expr Label Label
          | Guard  Expr Label
          | Goto   Label
          | Return Expr
          -- Array statements.
          -- They are here because some of them are stateful operations
          -- and they are backend specific.
          -- Perhaps there is a cleaner way to do this.
          | NewArray    Var  {- Array name -}
                        Expr {- Array length -}
          | ReadArray   Var  {- Variable to read into -}
                        Var  {- Array name -}
                        Expr {- Index -}
          | WriteArray  Var  {- Array name -}
                        Expr {- Index -}
                        Expr {- Element -}
          | ArrayLength Var  {- Variable to bind to -}
                        Var  {- Array name -}
          | SliceArray  Var  {- New array name (TODO: ugly) -}
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
arrLenStmt   = ArrayLength
sliceArrStmt = SliceArray


instance Construct Stmt where
  mapVars f stmt = go stmt
   where
    go (Bind v e) = Bind (f v) (mapVars f e)
    go (Assign v e) = Assign (f v) (mapVars f e)
    go (Case e l1 l2) = Case (mapVars f e) l1 l2
    go (Guard e l) = Guard (mapVars f e) l
    go (Goto l) = Goto l
    go (Return e) = Return (mapVars f e)
    go (NewArray v e) = NewArray (f v) (mapVars f e)
    go (ReadArray v1 v2 e) = ReadArray (f v1) (f v2) (mapVars f e)
    go (WriteArray v ei ex) = WriteArray (f v) (mapVars f ei) (mapVars f ex)
    go (ArrayLength v1 v2) = ArrayLength (f v1) (f v2)
    go (SliceArray v1 v2 e) = SliceArray (f v1) (f v2) (mapVars f e)


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


-- | Similar to @rewriteStmtLabels@ but rewrites index variables
--
-- TODO: Matching on variable name is ugly.
rewriteStmtRates :: IntDisjointSet -> Stmt -> Stmt
rewriteStmtRates rates = mapVars rw
  where
    rw v@(IdVar prefix uq)
      | prefix == indexPrefix
      = indexVar (Rates.representative uq rates)
      | otherwise
      = v
    rw v_ = v_


-------------------------------------------------------------------------------
-- * Loops

data Loop = Loop { -- | Loop entry block
                   loopEntry        :: Maybe Label

                   -- | Global arguments and their values
                 , loopArgs         :: (Map Var Arg)

                   -- | Resulting manifest array
                 , loopArrResult    :: Maybe Id  -- May not be the best way to represent this,
                                                 -- but currently the easiest.

                   -- | Resulting scalar result
                 , loopScalarResult :: Maybe Var


                   -- | The id of the loop whose @yield@ block produces the elements
                 , loopTheRate      :: Maybe Unique


                   -- | All the different rates of the loop, unified
                 , loopRates        :: IntDisjointSet


                   -- | Guard tests and increments that need to be inserted
                 , loopInsertIncrs  :: [Unique]  -- These are for the postprocessing step
                 , loopInsertTests  :: [Unique]  -- and should probably be dealt with more elegantly.


                   -- | Loop's basic blocks with their associated labels
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
    err = error $ "theSynonymLabel: label" +-+ show l +-+ "not found in sets"


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


-- | Retrieves an existing block out of the loop or returns and empty block
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


-- | Replace all statements (excluding final) in a block with the specified ones.
replaceStmts :: [Stmt] -> Label -> Loop -> Loop
replaceStmts stmts lbl = updateBlock lbl (setStmtsOfBlock stmts)


-- | Removes all statements from block (including final)
clearBlock :: Label -> Loop -> Loop
clearBlock lbl = updateBlock lbl (const emptyBlock)


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



-------------------------------------------------------------------------------
-- * Some loop field helper functions


addToInsertIncrs :: Unique -> Loop -> Loop
addToInsertIncrs uq loop = loop { loopInsertIncrs = uq : loopInsertIncrs loop }


addToInsertTests :: Unique -> Loop -> Loop
addToInsertTests uq loop = loop { loopInsertTests = uq : loopInsertTests loop }


removeFromInsertTests :: Unique -> Loop -> Loop
removeFromInsertTests uq loop = loop { loopInsertTests = modify $ loopInsertTests loop }
  where
    modify tests = delete uq
                 $ residual tests (loopRates loop)


setTheRate :: Unique -> Loop -> Loop
setTheRate uq loop = loop { loopTheRate = Just uq }


getJustRate :: Loop -> Unique
getJustRate loop = fromMaybe err (loopTheRate loop)
  where
    err = error 
        $ "getJustRate: This loop does not have the rate set." ++\ pprLoop loop



-------------------------------------------------------------------------------
-- * Scalar and Array results manipulation

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
pprStmt (ArrayLength i arr)     = "let" +-+ pprVar i +-+ "= arrayLength" +-+ pprVar arr
pprStmt (SliceArray arr' arr n) = "let" +-+ pprVar arr' +-+ "= sliceArray" +-+ pprVar arr +-+ pprExpr n
pprStmt (Return e)     = "return" +-+ pprExpr e
pprStmt _              = "pprStmt: Unknown Statement"


pprLabel :: Label -> String
pprLabel = show


instance Show Loop where
  show = pprLoop

pprLoop :: Loop -> String
pprLoop loop
    = "Loop Entry:    "  ++  maybe "None" pprLabel (loopEntry loop)                   ++\
      "Loop Args:     "  ++  (show $ Map.keys $ loopArgs loop)                        ++\
      "Array Result:  "  ++  maybe "None" (pprVar . arrayVar) (loopArrResult loop)    ++\
      "Scalar Result: "  ++  maybe "None" pprVar              (loopScalarResult loop) ++\
      "The rate:      "  ++  maybe "None" pprId               (loopTheRate loop)      ++\
      "Rates:         "  ++  show (loopRates loop)                                    ++\
      "To insert:" ++\
      "  Tests:       "  ++  show (loopInsertTests loop)                              ++\
      "  Inits/Incrs: "  ++  show (loopInsertIncrs loop)                              ++\
      "BlockMap:      "  ++\ pprBlockMap (loopBlockMap loop)


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


-- | A list of standard label constructors
stdLabelNames :: [Name]
stdLabelNames = [initNm, guardNm, bodyNm, yieldNm, bottomNm, doneNm]


initLbl, guardLbl, bodyLbl, yieldLbl, bottomLbl, doneLbl :: Id -> Label
initLbl   = Label initNm
guardLbl  = Label guardNm
bodyLbl   = Label bodyNm
yieldLbl  = Label yieldNm
bottomLbl = Label bottomNm
doneLbl   = Label doneNm


mkLabels :: [Name] -> Id -> [Label]
mkLabels names uq = map (\nm -> Label nm uq) names


-- | Add synonym labels for the basic predefined labels (init, guard, etc..)
addDefaultSynonymLabels :: Id -> Id -> Loop -> Loop
addDefaultSynonymLabels = addSynonymLabels stdLabelNames


-- | Add synonym labels for a given list of labels.
addSynonymLabels :: [Name] -> Id -> Id -> Loop -> Loop
addSynonymLabels labels nu old loop = foldl alias loop labels
  where
    alias loop lblName = addSynonymLabel (Label lblName nu) (Label lblName old) loop


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
touchDefaultBlocks uq loop = foldl (flip touchBlock) loop stdLabels
  where
    stdLabels = mkLabels stdLabelNames uq


-- | Add an empty block to the loop. Does nothing if the block exists
touchBlock :: Label -> Loop -> Loop
touchBlock label loop = updateBlock label id {-do nothing-} loop


-------------------------------------------------------------------------------


-- | Reduces the minimal set of labels
postprocessLoop :: Loop -> Loop
postprocessLoop loop = rewriteLoopLabelsAndRates
                     $ reorderDecls
                     $ writeResultArray uq
                     $ insertTests
                     $ insertIncrs
                     $ loop
  where
    uq  = fromMaybe err (loopArrResult loop)
    err = error "postprocessLoop: No array result set"


insertTests :: Loop -> Loop
insertTests loop = foldl insertTest loop rates
 where
  rates = Rates.residual (loopInsertTests loop) (loopRates loop)

  insertTest loop uq' = addStmt indexTest guard_
                      $ loop
   where
    uq        = Rates.representative uq' (loopRates loop)

    ix        = indexVar uq
    len       = lengthVar uq

    indexTest = guardStmt (fun2 ltInt ix len) done_

    guard_    = guardLbl  uq
    done_     = doneLbl   uq



insertIncrs :: Loop -> Loop
insertIncrs loop = foldl insertIncr loop rates
 where
  rates = Rates.residual (loopInsertIncrs loop) (loopRates loop)

  insertIncr loop uq' = addStmt indexInit init_
                      $ addStmt indexIncr bottom_
                      $ loop
   where
    uq        = Rates.representative uq' (loopRates loop)

    ix        = indexVar uq

    indexInit = bindStmt ix (TermE (0 :: Term Int))
    indexIncr = incStmt ix

    init_     = initLbl   uq
    bottom_   = bottomLbl uq


rewriteLoopLabelsAndRates :: Loop -> Loop
rewriteLoopLabelsAndRates loop
  = loop { loopBlockMap = newBlockMap
         , loopEntry    = newEntry }
  where
    lbls = AMap.keys $ loopBlockMap loop
    newEntry = theSynonymLabel lbls <$> loopEntry loop
    rates = loopRates loop
    newBlockMap = AMap.map (rewriteBlockLabelsAndRates lbls rates) (loopBlockMap loop)


writeResultArray :: Unique -> Loop -> Loop
writeResultArray uq loop = process loop
 where
  alloc   = newArrStmt arr (varE bound)
  write   = writeArrStmt arr (varE ix) (varE elt)
  slice   = sliceArrStmt resultVar arr (varE ix)
  ret     = returnStmt (varE resultVar)

  arr     = arrayVar  uq
  bound   = lengthVar uq
  ix      = indexVar  uq
  elt     = eltVar    uq

  process = addStmt alloc (initLbl uq)
        >>> addStmt write (yieldLbl uq)
        >>> addStmt slice (doneLbl uq)
        >>> addStmt ret   (doneLbl uq)


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
    isDecl (ArrayLength _ _) = True
    isDecl _            = False


{- loopEntry, loopArgs, loopArrResult, loopScalarResult, loopTheRate, loopRates, loopInsertIncrs, loopInsertTests, loopBlockMap -}
instance Monoid Loop where
  mempty = Loop Nothing Map.empty Nothing Nothing Nothing Rates.empty [] [] AMap.empty
  mappend loop1 loop2
    = Loop { loopEntry        = loopEntry    `joinWith` (<|>)
           , loopArgs         = loopArgs     `joinWith` Map.union
           , loopArrResult    = Nothing
           , loopScalarResult = Nothing
           , loopTheRate      = loopTheRate  `joinWith` (<|>)
           , loopRates        = loopRates    `joinWith` Rates.merge
           , loopInsertIncrs  = loopInsertTests `joinWith` (++)
           , loopInsertTests  = loopInsertIncrs `joinWith` (++)
           , loopBlockMap     = loopBlockMap `joinWith` AMap.unionWith appendLoopBlockMap
           }
    where
      joinWith :: (Loop  -> field)          -- field to take from loop
               -> (field -> field -> field) -- joining function
               -> field                     -- new field
      field `joinWith` f = f (field loop1) (field loop2)


append :: Loop -> Loop -> Loop
append = mappend


emptyLoop :: Loop
emptyLoop = mempty


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


instance Construct Expr where
  mapVars f = go
   where
    go (VarE v) = VarE (f v)
    go (AppE e1 e2) = AppE (mapVars f e1) (mapVars f e2)
    go e_ = e_


vAppE :: Var -> Var -> Expr
vAppE f x = AppE (varE f) (varE x)


varE :: Var -> Expr
varE = VarE


-- | Shorthand for applying a 1-argument function to a var.
fun1 :: (Elt a, Elt b) => (Term a -> Term b) -> Var -> Expr
fun1 f x = (TermE (lam f)) `AppE` (VarE x)


-- | Shorthand for applying a 2-argument function to a var.
fun2 :: (Elt a, Elt b, Elt c) => (Term a -> Term b -> Term c) -> Var -> Var -> Expr
fun2 f x y = (TermE (lam2 f)) `AppE` (VarE x) `AppE` (VarE y)


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
