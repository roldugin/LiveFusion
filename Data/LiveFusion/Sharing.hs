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
  Wrap :: Typeable t => ASG t s -> WrappedASG s


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
data ASG t s where
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

  ZipWith6G :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g)
            => (Term a -> Term b -> Term c -> Term d -> Term e -> Term f -> Term g)
            -> ArrayASG a s
            -> ArrayASG b s
            -> ArrayASG c s
            -> ArrayASG d s
            -> ArrayASG e s
            -> ArrayASG f s
            -> ArrayASG g s

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

  ReplicateG
            :: Elt a
            => Term Int
            -> Term a
            -> ArrayASG a s

  BpermuteG
           :: Elt a
           => ArrayASG a s
           -> ArrayASG Int s
           -> ArrayASG a s

  ManifestG :: Elt a
            => V.Vector a
            -> ArrayASG a s

  ScalarG   :: Elt a
            => Term a
            -> ScalarASG a s

  PackByBoolTagG
           :: Elt a 
           => Term Bool
           -> ArrayASG Bool s
           -> ArrayASG a s
           -> ArrayASG a s

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
            => Term Int
            -> ArrayASG Int s
            -> ArrayASG a s
            -> ArrayASG a s

  Indices_sG
            :: Term Int
            -> ArrayASG Int s
            -> ArrayASG Int s

  BothG     :: (Typeable t1, Typeable t2)
            => ASG t1 s
            -> ASG t2 s
            -> ASG (t1,t2) s

  VarG      :: Typeable t
            => s
            -> ASG t s


deriving instance Show s => Show (ASG t s)
deriving instance Typeable ASG


instance Typeable t => MuRef (AST t) where
  type DeRef (AST t) = WrappedASG
  mapDeRef ap t = Wrap <$> mapDeRef' ap t
    where
      mapDeRef' :: Applicative ap
                => (forall b. (MuRef b, WrappedASG ~ DeRef b) => b -> ap u)
                -> AST t
                -> ap (ASG t u)

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

      mapDeRef' ap (ZipWith6 f arr brr crr drr err frr)
        = ZipWith6G f
          <$> (VarG <$> ap arr)
          <*> (VarG <$> ap brr)
          <*> (VarG <$> ap crr)
          <*> (VarG <$> ap drr)
          <*> (VarG <$> ap err)
          <*> (VarG <$> ap frr)

      mapDeRef' ap (Fold f z arr)
        = FoldG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Scan f z arr)
        = ScanG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Replicate n x)
        = pure $ ReplicateG n x

      mapDeRef' ap (Bpermute arr ixs)
        = BpermuteG
          <$> (VarG <$> ap arr)
          <*> (VarG <$> ap ixs)

      mapDeRef' ap (PackByBoolTag tag tags arr)
        = PackByBoolTagG tag
          <$> (VarG <$> ap tags)
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

      mapDeRef' ap (Indices_s len segd)
        = Indices_sG len
          <$> (VarG <$> ap segd)

      mapDeRef' ap (Manifest vec)
        = pure $ ManifestG vec

      -- | Both Manifest and Manifest' map to ManifestG
      mapDeRef' ap (Manifest' vec)
        = pure $ ManifestG vec

      mapDeRef' ap (Scalar x)
        = pure $ ScalarG x

      mapDeRef' ap (Both ast1 ast2)
        = BothG
          <$> (VarG <$> ap ast1)
          <*> (VarG <$> ap ast2)


getASTNode :: Typeable t => Map Unique (WrappedASG Unique) -> Unique -> Maybe (ASG t Unique)
getASTNode m n = case m ! n of Wrap t -> cast t


recoverSharing :: Typeable t => AST t -> IO (Map Unique (WrappedASG Unique), Unique, Maybe (ASG t Unique))
recoverSharing t = do
  Graph l n <- reifyGraph t
  let m = Map.fromList l
  return (m, n, getASTNode m n)
{-# NOINLINE recoverSharing #-}
