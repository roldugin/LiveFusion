{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes,
             FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators, NamedFieldPuns, LambdaCase, ExplicitForAll #-}
module Data.LiveFusion.Sharing where

import Data.LiveFusion.AST
import Data.LiveFusion.Types hiding ( Unique )
import Data.LiveFusion.Scalar.HOAS as HOAS

import Control.Applicative
import Data.Map as Map hiding ( map, filter )
import Data.Reify
import Data.Reify.Graph
import Data.Typeable
import qualified Data.Vector.Unboxed as V


-- Required for getting data-reify to work with GADTs
data WrappedASG s where
  Wrap :: Typeable e => ASG e s -> WrappedASG s


deriving instance Show (WrappedASG Unique)


type ScalarASG a s = ASG a s
type ArrayASG a s = ASG (V.Vector a) s

-- The following fails for 2+ argument functions
--type family Fun t where
--  Fun (a -> b) = HOAS.Term a -> HOAS.Term b
--  Fun a = HOAS.Term a


-- | Abstract Semantic Graph is a directed acyclic graph derived from the AST
--   of delayed collective array operations by:
--   * Replacing every point of recursion with a uniquely named variable
--   * Eliminating common subexpressions and representing them as one node, reference by
--     variables of the same name.
data ASG e s where
  MapG      :: (Elt a, Elt b)
            => (Term a -> Term b)
            -> ArrayASG a s
            -> ArrayASG b s

  FilterG   :: Elt a
            => (Term a -> Term Bool)
            -> ArrayASG a s
            -> ArrayASG a s

  ZipWithG  :: (Elt a, Elt b, Elt c)
            => (Term a -> Term b -> Term c)
            -> ArrayASG a s
            -> ArrayASG b s
            -> ArrayASG c s

  ZipG      :: (Elt a, Elt b)
            => ArrayASG a s
            -> ArrayASG b s
            -> ArrayASG (a,b) s

  FoldG     :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG a s
            -> ScalarASG a s

  ScanG     :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG a s
            -> ArrayASG a s

  ManifestG :: Elt a
            => V.Vector a
            -> ArrayASG a s

  ScalarG   :: Elt a
            => Term a
            -> ScalarASG a s

  Fold_sG   :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG Int s
            -> ArrayASG a s
            -> ArrayASG a s

  Scan_sG   :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG Int s
            -> ArrayASG a s
            -> ArrayASG a s

  Replicate_sG
            :: Elt a
            => Int
            -> ArrayASG Int s
            -> ArrayASG a s
            -> ArrayASG a s

  VarG      :: Typeable e
            => s
            -> ASG e s


deriving instance Show s => Show (ASG e s)
deriving instance Typeable ASG


instance Typeable e => MuRef (AST e) where
  type DeRef (AST e) = WrappedASG
  mapDeRef ap e = Wrap <$> mapDeRef' ap e
    where
      mapDeRef' :: Applicative ap
                => (forall b. (MuRef b, WrappedASG ~ DeRef b) => b -> ap u)
                -> AST e
                -> ap (ASG e u)

      mapDeRef' ap (Map f arr)
        = MapG f
          <$> (VarG <$> ap arr)

      mapDeRef' ap (Filter p arr)
        = FilterG p
          <$> (VarG <$> ap arr)

      mapDeRef' ap (ZipWith f arr brr)
        = ZipWithG f
          <$> (VarG <$> ap arr)
          <*> (VarG <$> ap brr)

      mapDeRef' ap (Zip arr brr)
        = ZipG
          <$> (VarG <$> ap arr)
          <*> (VarG <$> ap brr)

      mapDeRef' ap (Fold f z arr)
        = FoldG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Scan f z arr)
        = ScanG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Fold_s f z lens arr)
        = Fold_sG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap lens)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Scan_s f z segd arr)
        = Scan_sG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap segd)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Replicate_s len segd arr)
        = Replicate_sG len
          <$> (VarG <$> ap segd)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Manifest vec)
        = pure $ ManifestG vec

      mapDeRef' ap (Scalar x)
        = pure $ ScalarG x


getASTNode :: Typeable e => Map Unique (WrappedASG Unique) -> Unique -> Maybe (ASG e Unique)
getASTNode m n = case m ! n of Wrap  e -> cast e


recoverSharing :: Typeable e => AST e -> IO (Map Unique (WrappedASG Unique), Unique, Maybe (ASG e Unique))
recoverSharing e = do
  Graph l n <- reifyGraph e
  let m = Map.fromList l
  return (m, n, getASTNode m n)
{-# NOINLINE recoverSharing #-}
