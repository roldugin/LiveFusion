{-# LANGUAGE TemplateHaskell #-}
module Data.LiveFusion.HsBackend.Prelude where

import Data.LiveFusion.Scalar.HOAS
import Data.LiveFusion.HsBackend.Impl
import Data.LiveFusion.Types

import Language.Haskell.TH as TH

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
minusTerm x y = (code minusImpl) `app` x `app` y

negateTerm :: IsNum a => Term a -> Term a
negateTerm x = (code negateImpl) `app` x

absTerm :: IsNum a => Term a -> Term a
absTerm x = (code absImpl) `app` x

signumTerm :: IsNum a => Term a -> Term a
signumTerm x = (code signumImpl) `app` x

fromIntegerTerm :: IsNum a => Integer -> Term a
fromIntegerTerm = code . fromIntegerImpl


-- Fractional -----------------------------------------------------------------

class (IsNum a, Fractional a, Typeable a, Show a) => IsFractional a

instance IsFractional Float
instance IsFractional Double

instance IsFractional a => Fractional (Term a) where
  (/) = divideTerm
  recip = recipTerm
  fromRational = fromRationalTerm

divideTerm :: IsFractional a => Term a -> Term a -> Term a
divideTerm x y = (code divideImpl) `app` x `app` y

recipTerm :: IsFractional a => Term a -> Term a
recipTerm x = (code recipImpl) `app` x

fromRationalTerm :: IsFractional a => Rational -> Term a
fromRationalTerm = code . fromRationalImpl


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


-------------------------------------------------------------------------------
-- * Booleans

true :: Term Bool
true = liftT0 $ mkImpl True [| True |]

false :: Term Bool
false = liftT0 $ mkImpl False [| False |]


-------------------------------------------------------------------------------
-- * Conditionals

-- | To use sugar if-then-else syntax set -XRebindableSyntax.
ifThenElse :: Elt a => Term Bool -> Term a -> Term a -> Term a
ifThenElse = liftT3 $ mkImpl hsExp [| \p x y -> case p of { True -> x ; False -> y } |]
    where hsExp p x y = case p of { True -> x; False -> y }


-------------------------------------------------------------------------------
-- * Tuples

fst :: (Elt a, Elt b) => Term (a,b) -> Term a
fst = liftT1 $ mkImpl Prelude.fst [| Prelude.fst |]

snd :: (Elt a, Elt b) => Term (a,b) -> Term b
snd = liftT1 $ mkImpl Prelude.snd [| Prelude.snd |]


infix 8 .*.
-- | Pair construction
(.*.) :: (Elt a, Elt b) => Term a -> Term b -> Term (a,b)
(.*.) = liftT2 $ mkImpl (,) tupConE
  where tupConE = TH.conE $ TH.mkName "(,)"


-------------------------------------------------------------------------------
-- * Lifting other Haskell functions (use mkImpl)

liftT0 :: (Elt a)
      => Impl a
      -> Term a
liftT0 impl = code impl


liftT1 :: (Elt a, Elt b)
      => Impl (a -> b)
      -> Term a -> Term b
liftT1 impl x = (code impl) `app` x


liftT2 :: (Elt a, Elt b, Elt c)
       => Impl (a -> b -> c)
       -> Term a -> Term b -> Term c
liftT2 impl x y = (code impl) `app` x `app` y


liftT3 :: (Elt a, Elt b, Elt c, Elt d)
       => Impl (a -> b -> c -> d)
       -> Term a -> Term b -> Term c -> Term d
liftT3 impl x y z = (code impl) `app` x `app` y `app` z

