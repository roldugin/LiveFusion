{-# LANGUAGE ViewPatterns #-}
module Data.LiveFusion.Loop.Postprocess where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.LoopType
import Data.LiveFusion.Loop.Block
import Data.LiveFusion.Loop.Stmt
import Data.LiveFusion.Loop.Expr
import Data.LiveFusion.Loop.Label
import Data.LiveFusion.Loop.Var

import Data.LiveFusion.Scalar.HOAS as HOAS

import Data.LiveFusion.DisjointSet as Rates
import Data.LiveFusion.AliasMap ( AliasMap )
import qualified Data.LiveFusion.AliasMap as AMap
import Data.LiveFusion.Util

import Data.Maybe
import Data.List
import Data.Functor ( (<$>) )
import Control.Arrow ( (>>>) )


-- | Reduces the minimal set of labels
postprocessLoop :: Loop -> Loop
postprocessLoop loop = rewriteLoopLabelsAndRates
                     $ reorderDecls
                     $ removeClashingStmts
                     $ writeResultArray uq
                     $ maybeNestLoops
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


-- | Inserts statements allowing the nesting to happen
-- @
--  nest_segd:
--    seglen = readArray arr_segd i_segd
--    segend = i_data + seglen
--    goto guard_data
--  guard_data:
--    unless i_data < segend | body_segd
--  body_segd:
--    ...
-- @
maybeNestLoops :: Loop -> Loop
maybeNestLoops loop@(getNesting -> Nothing) = loop
maybeNestLoops loop@(getNesting -> Just (segd_uq, data_uq)) = loop'
 where
  segelt     = eltVar segd_uq

  -- nest_segd (run before each segment, acts like init for inner loop)
  seglenVar  = lengthVar segd_uq
  segendVar  = var "end" segd_uq  -- end of segment index
  segendSet  = bindStmt segendVar (fun2 plusInt ixVar segelt)
  nest_segd_stmts = [segendSet]

  -- guard_data (have we reached the end of segment?)
  ixVar      = indexVar data_uq
  segendTest = guardStmt (fun2 ltInt ixVar segendVar) body_segd
  guard_data_stmts = [segendTest]
  
  -- labels
  init_      = initLbl segd_uq
  guard_segd = guardLbl segd_uq
  nest_segd  = nestLbl segd_uq
  body_segd  = bodyLbl segd_uq
  guard_data = guardLbl data_uq

  -- THE loop
  loop'      = id
             -- Start with outer (segd) loop
             $ setFinalGoto init_ guard_segd
             -- Enter inner loop after setting up segment bounds
             $ setFinalGoto nest_segd guard_data
             $ addStmts nest_segd_stmts nest_segd
             $ addStmts guard_data_stmts guard_data
             $ moveWithDeps segelt body_segd nest_segd
             $ loop


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
