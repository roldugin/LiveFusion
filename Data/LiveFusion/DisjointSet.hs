module Data.LiveFusion.DisjointSet
	( module Data.IntDisjointSet
	, merge
	, unionInsert ) where

import Data.IntDisjointSet hiding ( map )


-- | A safe variant of merge.
merge :: IntDisjointSet -> IntDisjointSet -> IntDisjointSet
merge s1 s2 = fromList $ (fst $ toList s1) ++ (fst $ toList s2)


-- | An insert followed by union.
unionInsert :: Int -> Int -> IntDisjointSet -> IntDisjointSet
unionInsert n1 n2 = union n1 n2
                  . insert n1
                  . insert n2