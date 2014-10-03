{-# LANGUAGE GADTs, PatternGuards, StandaloneDeriving #-}

-- | Loop is a representation of a DSL with basic blocks
--   and explicit control flow using goto's.
--
--   It can be used for things other than loops since there is
--   no fixed loop structure but probably shouldn't.
--
--   The language offers statements for direct array manipulation.
module Data.LiveFusion.Loop
  ( module Data.LiveFusion.Loop
  , module Data.LiveFusion.Loop.Common
  , module Data.LiveFusion.Loop.BlockMap
  , module Data.LiveFusion.Loop.Block
  , module Data.LiveFusion.Loop.Stmt
  , module Data.LiveFusion.Loop.Expr
  , module Data.LiveFusion.Loop.Label
  , module Data.LiveFusion.Loop.Var ) where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.BlockMap
import Data.LiveFusion.Loop.Block
import Data.LiveFusion.Loop.Stmt
import Data.LiveFusion.Loop.Expr
import Data.LiveFusion.Loop.Label
import Data.LiveFusion.Loop.Var

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
-- * Block

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


                   -- | Guard tests and index initialisation/increments that need *not* be inserted
                 , loopSkipTests    :: [Unique]  -- These are for the postprocessing step
                 , loopSkipIncrs    :: [Unique]  -- and should probably be dealt with more elegantly.


                   -- | Loop's basic blocks with their associated labels
                 , loopBlockMap     :: BlockMap
                 }




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
rewriteStmtLabels lbls = mapLabels rw
  where
    rw l = theSynonymLabel lbls l


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


addToSkipIncrs :: Unique -> Loop -> Loop
addToSkipIncrs uq loop = loop { loopSkipIncrs = uq : loopSkipIncrs loop }


addToSkipTests :: Unique -> Loop -> Loop
addToSkipTests uq loop = loop { loopSkipTests = uq : loopSkipTests loop }


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


instance Show Loop where
  show = pprLoop

pprLoop :: Loop -> String
pprLoop loop
    = "Loop Entry:    "  ++  maybe "None" pprLabel (loopEntry loop)                   ++\
      "Loop Args:     "  ++  (show $ Map.keys $ loopArgs loop)                        ++\
      "Array Result:  "  ++  maybe "None" (pprVar . arrayVar) (loopArrResult loop)    ++\
      "Scalar Result: "  ++  maybe "None" pprVar              (loopScalarResult loop) ++\
      "The rate:      "  ++  maybe "None" pprId               (loopTheRate loop)      ++\
      "Rates:         "  ++  pprDisjointSet (loopRates loop)                          ++\
      "Skip inserting:" ++\
      "  Inits/Incrs: "  ++  show (loopSkipIncrs loop)                                ++\
      "  Tests:       "  ++  show (loopSkipTests loop)                                ++\
      "BlockMap:      "  ++\ pprBlockMap (loopBlockMap loop)


--------------------------------------------------------------------------------


addArg var arg loop = loop { loopArgs = loopArgs' }
  where loopArgs' = Map.insert var arg (loopArgs loop)


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
                     $ removeClashingStmts
                     $ writeResultArray uq
                     $ insertTests
                     $ insertIncrs
                     $ loop
  where
    uq  = fromMaybe err (loopArrResult loop)
    err = error "postprocessLoop: No array result set"


insertTests :: Loop -> Loop
insertTests loop = foldl insertTest loop toInsert
 where
  toInsert = allRates \\ toSkip
  toSkip   = Rates.residual (loopSkipTests loop) (loopRates loop)
  allRates = representatives (loopRates loop)

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
insertIncrs loop = foldl insertIncr loop toInsert
 where
  toInsert = allRates \\ toSkip
  toSkip   = Rates.residual (loopSkipIncrs loop) (loopRates loop)
  allRates = representatives (loopRates loop)

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

    reorder = sortBy orderStmts


-- | Sometimes multiple binings of the same variable get generated.
--
-- For example when fusing @zipWith f xs xs@, two duplicate length and element
-- bindings will appear for each of the @xs@.
--
-- Note that it doesn't touch the final stmt
-- TODO: Abstract traversal into mapBlocks
removeClashingStmts :: Loop -> Loop
removeClashingStmts loop = loop { loopBlockMap = AMap.map perblock (loopBlockMap loop) }
  where
    perblock (Block stmts final) = Block (nubBy clash stmts) final


{- loopEntry, loopArgs, loopArrResult, loopScalarResult, loopTheRate, loopRates, loopInsertIncrs, loopInsertTests, loopBlockMap -}
instance Monoid Loop where
  mempty = Loop Nothing Map.empty Nothing Nothing Nothing Rates.empty [] [] AMap.empty
  mappend loop1 loop2
    = Loop { loopEntry        = loopEntry     `joinWith` (<|>)
           , loopArgs         = loopArgs      `joinWith` Map.union
           , loopArrResult    = Nothing
           , loopScalarResult = Nothing
           , loopTheRate      = loopTheRate   `joinWith` (<|>)
           , loopRates        = loopRates     `joinWith` Rates.merge
           , loopSkipIncrs    = loopSkipIncrs `joinWith` (++)
           , loopSkipTests    = loopSkipTests `joinWith` (++)
           , loopBlockMap     = loopBlockMap  `joinWith` AMap.unionWith appendLoopBlockMap
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
