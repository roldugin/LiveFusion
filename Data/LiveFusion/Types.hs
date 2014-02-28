{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleContexts, StandaloneDeriving, TemplateHaskell, KindSignatures, RankNTypes #-}
module Data.LiveFusion.Types where

import Data.LiveFusion.HSBackend

import qualified Data.Vector.Unboxed as V
import Data.Typeable
import Data.Word
import Data.Maybe
import Control.Applicative
import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH ( Q )
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

-------------------------------------------------------------------------------
-- Functions ------------------------------------------------------------------

instance Num a => Num (Exp a) where
  (+) = plusExp
  (*) = timesExp
  (-) = minusExp

  negate = negateExp

  abs = absExp

  signum = signumExp

  fromInteger = fromIntegerExp

data Exp a where
  ConstE :: a -> Exp a
  ExtE :: Impl a -> Exp a
  AppE :: Exp (a -> b) -> Exp a -> Exp b


instance Functor Exp where
  fmap f x = ExtE (nofuse_pureImpl f) <*> x
instance Applicative Exp where
  pure = ConstE
  f <*> x = AppE f x

plusExp, timesExp, minusExp :: Num a => Exp a -> Exp a -> Exp a
plusExp x y = (ExtE plusImpl) <*> x <*> y
timesExp x y = (ExtE timesImpl) <*> x <*> y
minusExp x y = (ExtE timesImpl) <*> x <*> y

negateExp :: Num a => Exp a -> Exp a
negateExp x = (ExtE negateImpl) <*> x

absExp :: Num a => Exp a -> Exp a
absExp x = (ExtE absImpl) <*> x

signumExp :: Num a => Exp a -> Exp a
signumExp x = (ExtE signumImpl) <*> x

fromIntegerExp :: Num a => Integer -> Exp a
fromIntegerExp = ConstE . fromInteger


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

