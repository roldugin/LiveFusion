{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes,
             FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators, NamedFieldPuns, LambdaCase, ExplicitForAll #-}
module Data.LiveFusion.AST where

import Data.LiveFusion.Types
import Data.LiveFusion.Scalar.HOAS as HOAS

import Data.Typeable
import Data.Vector.Unboxed as V hiding ( (++) )


type ScalarAST a = AST a
type ArrayAST a = AST (V.Vector a)


-- | Abstract Syntax Tree whose nodes represent delayed collective array operations.
data AST t where
  Map      :: (Elt a, Elt b)
           => (Term a -> Term b)
           -> ArrayAST a
           -> ArrayAST b

  Filter   :: Elt a
           => (Term a -> Term Bool)
           -> ArrayAST a
           -> ArrayAST a

  ZipWith  :: (Elt a, Elt b, Elt c)
           => (Term a -> Term b -> Term c)
           -> ArrayAST a
           -> ArrayAST b
           -> ArrayAST c

  ZipWith6 :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g)
           => (Term a -> Term b -> Term c -> Term d -> Term e -> Term f -> Term g)
           -> ArrayAST a
           -> ArrayAST b
           -> ArrayAST c
           -> ArrayAST d
           -> ArrayAST e
           -> ArrayAST f
           -> ArrayAST g

  Fold     :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST a
           -> ScalarAST a

  Scan     :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST a
           -> ArrayAST a

  Replicate
           :: Elt a
           => Term Int
           -> Term a
           -> ArrayAST a

  Bpermute 
           :: Elt a 
           => ArrayAST a
           -> ArrayAST Int
           -> ArrayAST a

  PackByBoolTag
           :: Elt a 
           => Term Bool
           -> ArrayAST Bool
           -> ArrayAST a
           -> ArrayAST a

  Fold_s   :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST Int
           -> ArrayAST a
           -> ArrayAST a

  Scan_s   :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST Int
           -> ArrayAST a
           -> ArrayAST a

  Replicate_s
           :: Elt a
           => Term Int
           -> ArrayAST Int
           -> ArrayAST a
           -> ArrayAST a

  Indices_s
           :: Term Int
           -> ArrayAST Int
           -> ArrayAST Int

  Manifest :: Elt a
           => V.Vector a
           -> ArrayAST a

  -- | TODO We use this one when we need to prevent
  --   observable sharing. It's largely a hack.
  Manifest':: Elt a
           => V.Vector a
           -> ArrayAST a

  Scalar   :: Elt a
           => Term a
           -> ScalarAST a

  -- | For computing multiple results at the same time
  Both     :: (Typeable t1, Typeable t2)
           => AST t1
           -> AST t2
           -> AST (t1,t2)


-- | Shorthand for AST.Both constructor.
(|*|) :: (Typeable t1, Typeable t2)
      => AST t1 -> AST t2 -> AST (t1,t2)
(|*|) = Both


-- | Traverse AST calling the given function for each node.
--
-- You probably want the two functions to be mutually recursive.
trav :: (forall t1 . AST t1 -> AST t1)
     -> AST t -> AST t
trav ap = go
 where
  go (Map f a) = Map f (ap a)
  go (Filter p a)  = Filter p (ap a)
  go (ZipWith f a b) = ZipWith f (ap a) (ap b)
  go (ZipWith6 f' a b c d e f) = ZipWith6 f' (ap a) (ap b) (ap c) (ap d) (ap e) (ap f)
  go (Fold f z a) = Fold f z (ap a)
  go (Scan f z a) = Scan f (ap z) (ap a)
  go (Replicate n x) = Replicate n x
  go (Bpermute a i) = Bpermute (ap a) (ap i)
  go (PackByBoolTag t ts a) = PackByBoolTag t (ap ts) (ap a)
  go (Fold_s f z s a) = Fold_s f (ap z) (ap s) (ap a)
  go (Scan_s f z s a) = Scan_s f (ap z) (ap s) (ap a)
  go (Replicate_s n s a) = Replicate_s n (ap s) (ap a)
  go (Indices_s n s) = Indices_s n (ap s)
  go (Manifest v) = Manifest v
  go (Manifest' v) = Manifest' v
  go (Scalar v) = Scalar v


-- | Rebases AST on top of Manifest' instead of Manifest
rebaseManifest' :: AST t -> AST t
rebaseManifest' (Manifest vec) = Manifest' vec
rebaseManifest' ast = trav rebaseManifest' ast


showAST :: AST t -> String
showAST (Map _ arr) = "Map (" ++ (showAST arr) ++ ")"
showAST (Filter _ arr) = "Filter (" ++ (showAST arr) ++ ")"
showAST (ZipWith _ arr brr) = "ZipWith (" ++ (showAST arr) ++ ") (" ++ (showAST brr) ++ ")"
showAST (Fold _ _ arr) = "Fold (" ++ (showAST arr) ++ ")"
showAST (Manifest vec) = show vec
