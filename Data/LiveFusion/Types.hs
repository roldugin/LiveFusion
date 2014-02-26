{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleContexts, StandaloneDeriving #-}
module Data.LiveFusion.Types where

import qualified Data.Vector.Unboxed as V
import Data.Typeable
import Data.Word
import Data.Maybe

import Prelude as P


class (Show a, V.Unbox a, Typeable a) => Elt a

instance Elt Int
instance Elt Float
instance Elt Double
instance Elt Bool
instance Elt Word8
instance (Elt a, Elt b) => Elt (a,b)
instance (Elt a, Elt b, Elt c) => Elt (a,b,c)
instance (Elt a, Elt b, Elt c, Elt d) => Elt (a,b,c,d)


class Fun1 f where
  apply1 :: f a b -> Maybe (a -> b)
  apply1 _ = Nothing

  code1  :: f a b -> Maybe (String)
  code1  _ = Nothing

  vect1  :: f a b -> Maybe ([a] -> [b])
  vect1  _ = Nothing


class Fun2 f where
  apply2 :: f a b c -> Maybe (a -> b -> c)
  apply2 _ = Nothing

  code2  :: f a b c -> Maybe (String)
  code2  _ = Nothing

  vect2  :: f a b c -> Maybe ([a] -> [b] -> [c])
  vect2  _ = Nothing


class Fun3 f where
  apply3 :: f a b c d -> Maybe (a -> b -> c -> d)
  apply3 _ = Nothing

  code3  :: f a b c d -> Maybe (String)
  code3  _ = Nothing

  vect3  :: f a b c d -> Maybe ([a] -> [b] -> [c] -> [d])
  vect3  _ = Nothing


data GenericFun1 a b = GenericFun1 (a -> b)
instance Fun1 GenericFun1 where
  apply1 (GenericFun1 f) = Just f
  vect1 (GenericFun1 f) = Just (P.map f)


data GenericFun2 a b c = GenericFun2 (a -> b -> c)
instance Fun2 GenericFun2 where
  apply2 (GenericFun2 f) = Just f
  vect2 (GenericFun2 f) = Just (P.zipWith f)


data GenericFun3 a b c d = GenericFun3 (a -> b -> c -> d)
instance Fun3 GenericFun3 where
  apply3 (GenericFun3 f) = Just f
  vect3 (GenericFun3 f) = Just (P.zipWith3 f)


-------------------------------------------------------------------------------
-- Some functions defined in terms of GenericFun ------------------------------

plusFun :: Num a => GenericFun2 a a a
plusFun = GenericFun2 (P.+)

gtFun :: Ord a => GenericFun2 a a Bool
gtFun = GenericFun2 (P.>)

idFun :: GenericFun1 a a
idFun = GenericFun1 (P.id)

divideFun :: Fractional a => GenericFun2 a a a
divideFun = GenericFun2 (P./)


-------------------------------------------------------------------------------
-- Some functions defined in terms of Fun type class --------------------------

data PlusFun a b c where
  PlusFun :: Num a => PlusFun a a a
instance Fun2 PlusFun where
  apply2 PlusFun = Just (P.+)
  code2 PlusFun = Just "Prelude.+"
  vect2 PlusFun = Just (P.zipWith (P.+))

data GtFun a b c where
  GtFun :: Ord a => GtFun a a Bool
instance Fun2 GtFun where
  apply2 GtFun = Just (P.>)
  code2 GtFun = Just "Prelude.>"
  vect2 GtFun = Just (P.zipWith (P.>))

data DivideFun a b c where
  DivideFun :: Fractional a => DivideFun a a a
instance Fun2 DivideFun where
  apply2 DivideFun = Just (P./)
  code2 DivideFun = Just "Prelude./"
  vect2 DivideFun = Just (P.zipWith (P./))


-------------------------------------------------------------------------------
-- Composable unary functions -------------------------------------------------
--class Impl f where
--  hs :: f a -> a
--  th :: f a -> String

--data Inc a where
--  Inc :: Num a => Inc (a -> a)
--instance Impl Inc where
--  hs Inc = (+1)
--  th Inc = "\\x -> x + 1"

--data Plus a where
--  Plus :: Num a => Plus (a -> a -> a)
--instance Impl Plus where
--  hs Plus = (+)
--  th Plus = "\\x y -> x + y"

data Exp a where
  ConstE :: a -> Exp a
  ExtE :: Impl a -> Exp a
  AppE :: Exp (a -> b) -> Exp a -> Exp b


data Impl a = Impl {  hs :: a
                   ,  th :: String
                   }


incI :: Num a => Impl (a -> a)
incI = Impl { hs = (+1)
            , th = "\\x -> x + 1"
            }


plusI :: Num a => Impl (a -> a -> a)
plusI = Impl { hs = (+)
             , th = "\\x y -> x + y"
             }


inc :: Num a => Exp a -> Exp a
inc n = (ExtE incI) `AppE` n


plus :: Num a => Exp a -> Exp a -> Exp a
plus x y = (ExtE plusI) `AppE` x `AppE` y


-------------------------------------------------------------------------------
-- AST ------------------------------------------------------------------------

type ArrayAST a = AST (Data a)

type ScalarAST a = AST a

type Data a = [a]

data AST a where
  Scal     :: a -> ScalarAST a
  Manifest :: [a] -> ArrayAST a
  Map      :: Exp (a -> b) -> ArrayAST a -> ArrayAST b
  ZipWith  :: Exp (a -> b -> c) -> ArrayAST a -> ArrayAST b -> ArrayAST c
  Fold     :: Exp (a -> b -> a) -> ScalarAST a -> ArrayAST b -> AST a


-------------------------------------------------------------------------------
-- Frontend -------------------------------------------------------------------

-- User facing array type
type Array a = ArrayAST a

type Scalar a = ScalarAST a


-- User combinator function
map' :: Exp (a -> b) -> Array a -> Array b
map' f arr = Map f arr

zipWith' :: Exp (a -> b -> c) -> Array a -> Array b -> Array c
zipWith' f arr brr = ZipWith f arr brr

fold' :: Exp (a -> b -> a) -> Scalar a -> Array b -> Scalar a
fold' f z arr = Fold f z arr

use :: a -> Scalar a
use = Scal

ret :: Scalar a -> a
ret = eval

fromList' :: [a] -> Array a
fromList' = Manifest

toList' :: Array a -> [a]
toList' = eval

(!) :: Array a -> Int -> a
arr ! i = (toList' arr) !! i


-------------------------------------------------------------------------------
-- Backend selection ----------------------------------------------------------

eval :: AST a -> a
eval = evalI


-------------------------------------------------------------------------------
-- Interpreter Backend --------------------------------------------------------

evalI :: AST a -> a
evalI (Scal x) = x
evalI (Manifest xs) = xs
--evalI (Map f xs) = P.map (hs f) (eval xs)
--evalI (ZipWith f xs ys) = P.zipWith (hs f) (eval xs) (eval ys)
--evalI (Fold f z xs) = P.foldl (hs f) (eval z) (eval xs)

