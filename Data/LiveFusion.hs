{-# LANGUAGE TypeFamilies, TypeSynonymInstances, FlexibleInstances #-}
module Data.LiveFusion where

import Data.LiveFusion.AST
import Data.LiveFusion.Combinators
import Data.LiveFusion.Types
import Data.LiveFusion.Scalar.HOAS

import Data.LiveFusion.HsBackend.Prelude

import Prelude hiding ( map, filter, zipWith, zipWith3, zip )

import Data.Vector.Unboxed as V ( toList, fromList, (!) )
import GHC.Exts

type Array a = ArrayAST a

map :: (Elt a, Elt b) => (Term a -> Term b) -> Array a -> Array b
map f = Map f

filter :: (Elt a) => (Term a -> Term Bool) -> Array a -> Array a
filter p = Filter p

zipWith :: (Elt a, Elt b, Elt c) => (Term a -> Term b -> Term c) -> Array a -> Array b -> Array c
zipWith f arr brr = ZipWith f arr brr

zip :: (Elt a, Elt b) => Array a -> Array b -> Array (a,b)
zip arr brr = Zip arr brr

fold :: Elt a => (Term a -> Term a -> Term a) -> Term a -> Array a -> a
fold f z arr = evalAST $ Fold f (Scalar z) arr

scan :: Elt a => (Term a -> Term a -> Term a) -> Term a -> Array a -> Array a
scan f z arr = Scan f (Scalar z) arr

scan_s :: Elt a => (Term a -> Term a -> Term a) -> Term a -> Array Int -> Array a -> Array a
scan_s f z arr = Scan_s f (Scalar z) arr

fold_s :: Elt a => (Term a -> Term a -> Term a) -> Term a -> Array Int -> Array a -> Array a
fold_s f z arr = Fold_s f (Scalar z) arr

-- | Indexing
--
-- Use only after @force@.
-- Otherwise the array will be recomputed for every lookup.
(!) :: Elt a => Array a -> Int -> a
arr ! ix
  = let vec = eval arr
    in vec V.! ix

force :: Elt a => Array a -> Array a
force = Manifest . eval

toList :: Elt a => Array a -> [a]
toList = V.toList . eval

fromList :: Elt a => [a] -> Array a
fromList = Manifest . V.fromList

-- | An instance for OverloadLists.
--
-- It makes it possible to use regular list syntax to construct arrays:
-- @ map (+1) [1,2,3] @
--
-- NOTE: Must enable OverloadedLists extension by using the following pragma:
-- @{-# LANGUAGE OverloadedLists #-}@
-- Or in GHCi:
-- @:set -XOverloadedLists@
instance Elt a => IsList (Array a) where
  type Item (Array a) = a
  fromList  = Data.LiveFusion.fromList
  toList    = Data.LiveFusion.toList
