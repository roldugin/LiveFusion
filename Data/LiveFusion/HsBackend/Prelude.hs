module Data.LiveFusion.HsBackend.Prelude where

import Data.LiveFusion.Scalar.HOAS
import Data.LiveFusion.HsBackend

import Data.Typeable


-- | Shorthand class for `Num` which can be used in `HOAS.Term` tree.
class (Num a, Typeable a, Show a) => IsNum a

instance IsNum a => Num (Term a) where
  (+) = plusTerm
  (*) = timesTerm
  (-) = minusTerm

  negate = negateTerm

  abs = absTerm

  signum = signumTerm

  fromInteger = fromIntegerTerm

plusTerm, timesTerm, minusTerm :: IsNum a => Term a -> Term a -> Term a
plusTerm x y = (code plusImpl) `app` x `app` y
timesTerm x y = (code timesImpl) `app` x `app` y
minusTerm x y = (code timesImpl) `app` x `app` y

negateTerm :: IsNum a => Term a -> Term a
negateTerm x = (code negateImpl) `app` x

absTerm :: IsNum a => Term a -> Term a
absTerm x = (code absImpl) `app` x

signumTerm :: IsNum a => Term a -> Term a
signumTerm x = (code signumImpl) `app` x

fromIntegerTerm :: IsNum a => Integer -> Term a
fromIntegerTerm = con . fromInteger
