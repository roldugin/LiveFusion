module Data.LiveFusion.DisjointSet
	( module Data.IntDisjointSet
	, merge
	, unionInsert
	, representative ) where

import Data.LiveFusion.Util

import Data.IntDisjointSet hiding ( map )
import Data.Maybe
import Prelude hiding ( lookup )


-- | A safe variant of merge.
merge :: IntDisjointSet -> IntDisjointSet -> IntDisjointSet
merge s1 s2 = fromList $ (fst $ toList s1) ++ (fst $ toList s2)


-- | An insert followed by union.
unionInsert :: Int -> Int -> IntDisjointSet -> IntDisjointSet
unionInsert n1 n2 = union n1 n2
                  . insert n1
                  . insert n2


-- | Unsafe, non-balancing lookup
representative :: Int -> IntDisjointSet -> Int
representative n set = fromMaybe err (fst $ lookup n set)
 where
  err = error $ "DisjointSet: Item" +-+ show n +-+ "is not represented in set" +-+ show set
