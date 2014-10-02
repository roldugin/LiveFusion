module Data.LiveFusion.DisjointSet
	( module Data.IntDisjointSet
	, merge
	, unionInsert
	, representative
	, representatives
	, residual
	, subsets
	, pprDisjointSet ) where

import Data.LiveFusion.Util

import Data.IntDisjointSet hiding ( map )
import Data.List ( nub, sortBy, groupBy, sort )
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


-- | A list of all representatives of the set
representatives :: IntDisjointSet -> [Int]
representatives = nub            -- [3,1]
                . map snd        -- [   3 ,   3 ,   1 ,   3 ]
                . fst . toList   -- [(4,3),(3,3),(1,1),(2,3)]


-- | Unsafe, non-balancing lookup
representative :: Int -> IntDisjointSet -> Int
representative n set = fromMaybe err (fst $ lookup n set)
 where
  err = error $ "DisjointSet: Item" +-+ show n +-+ "is not represented in set" +-+ show set


-- | Returns only unique representatives of elements in a list.
--
-- Note: All elements must be present in the set, otherwise the function will fail.
residual :: [Int] -> IntDisjointSet -> [Int]
residual list set = nub $ map (\x -> representative x set) list


subsets :: IntDisjointSet -> [[Int]]
subsets = sort
	    . map (map fst)
	    . groupBy eqSnds
	    . sortBy cmpSnds
        . fst . toList
  where
  	cmpSnds (_,x) (_,y) = compare x y
  	eqSnds  (_,x) (_,y) = x == y


pprDisjointSet :: IntDisjointSet -> String
pprDisjointSet = show . subsets
