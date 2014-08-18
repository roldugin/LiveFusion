module Data.LiveFusion.HsBackend.Prelude where

import Data.LiveFusion.Scalar.HOAS
import Data.LiveFusion.HsBackend

import Data.Typeable


-- Num ------------------------------------------------------------------------

-- | Shorthand class for `Num` which can be used in `HOAS.Term` tree.
class (Num a, Typeable a, Show a) => IsNum a

instance IsNum Int
instance IsNum Float
instance IsNum Double

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
fromIntegerTerm = code . fromIntegerImpl


-- Eq -------------------------------------------------------------------------

class (Eq a, Typeable a, Show a) => IsEq a where
  (==.), (/=.) :: Term a -> Term a -> Term Bool
  (==.) = eqTerm
  (/=.) = neTerm

instance IsEq Int
instance IsEq Float
instance IsEq Double
instance IsEq Bool

--deriving instance (IsEq a, IsEq b) => IsEq (a,b)

eqTerm, neTerm :: IsEq a => Term a -> Term a -> Term Bool
eqTerm x y = (code eqImpl) `app` x `app` y
neTerm x y = (code neImpl) `app` x `app` y


-- Ord ------------------------------------------------------------------------

class (Ord a, Typeable a, Show a) => IsOrd a where
  -- skipped compare
  (<.), (<=.), (>.), (>=.) :: Term a -> Term a -> Term Bool
  (<.)  = ltTerm
  (<=.) = leTerm
  (>.)  = gtTerm
  (>=.) = geTerm

  max', min'               :: Term a -> Term a -> Term a
  min' = minTerm
  max' = maxTerm

instance IsOrd Int
instance IsOrd Float
instance IsOrd Double

ltTerm, leTerm, gtTerm, geTerm :: IsOrd a => Term a -> Term a -> Term Bool
ltTerm x y = (code ltImpl) `app` x `app` y
leTerm x y = (code leImpl) `app` x `app` y
gtTerm x y = (code gtImpl) `app` x `app` y
geTerm x y = (code geImpl) `app` x `app` y

minTerm, maxTerm :: IsOrd a => Term a -> Term a -> Term a
minTerm x y = (code minImpl) `app` x `app` y
maxTerm x y = (code maxImpl) `app` x `app` y
