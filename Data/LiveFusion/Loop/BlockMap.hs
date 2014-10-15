module Data.LiveFusion.Loop.BlockMap where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.Block
import Data.LiveFusion.Loop.Label

import Data.LiveFusion.AliasMap ( AliasMap )
import qualified Data.LiveFusion.AliasMap as AMap
import Data.LiveFusion.Util

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Set ( Set )
import qualified Data.Set as Set


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



--------------------------------------------------------------------------------
-- * Pretty printing

pprBlockMap :: BlockMap -> String
pprBlockMap = unlines . map pprOne . sortOnKeysBy cmp . AMap.assocs
  where
    pprOne (lbls, blk) = (pprLabels lbls) ++
                         (indent 1 $ pprBlock blk)

    -- Note that this assumes all label names to be the same with different ids.
    pprLabels lblSet = let lbls@(first:_) = Set.toList lblSet
                           pprLabelName (Label nm _) = pprName nm
                           pprLabelId   (Label _ n) = "_" ++ pprId n
                       in  pprLabelName first ++ intercalateMap "/" pprLabelId lbls ++ ":\n"


    cmp :: Set Label -> Set Label -> Ordering
    cmp s1 s2 = let Label nm1 id1 = theOneLabel s1
                    Label nm2 id2 = theOneLabel s2
                in  compare id1 id2 `thenCmp` fixedCompare stdLabelNames nm1 nm2
