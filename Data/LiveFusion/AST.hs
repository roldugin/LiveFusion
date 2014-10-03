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
data AST e where
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

  Zip      :: (Elt a, Elt b)
           => ArrayAST a
           -> ArrayAST b
           -> ArrayAST (a,b)

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

  Scalar   :: Elt a
           => Term a
           -> ScalarAST a


showAST :: AST e -> String
showAST (Map _ arr) = "Map (" ++ (showAST arr) ++ ")"
showAST (Filter _ arr) = "Filter (" ++ (showAST arr) ++ ")"
showAST (ZipWith _ arr brr) = "ZipWith (" ++ (showAST arr) ++ ") (" ++ (showAST brr) ++ ")"
showAST (Zip arr brr) = "Zip (" ++ (showAST arr) ++ ") (" ++ (showAST brr) ++ ")"
showAST (Fold _ _ arr) = "Fold (" ++ (showAST arr) ++ ")"
showAST (Manifest vec) = show vec
