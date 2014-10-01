{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.LiveFusion.HsBackend.THDefinitions where

-- | The use of Exp is a little overloaded in this code base. In this module
--   all references to Exp are TemplateHaskell expressions defined in
--   Language.Haskell.TH
import Language.Haskell.TH as TH
import Language.Haskell.TH.Syntax
import Data.Ratio

-------------------------------------------------------------------------------
-- class (Eq a)
eqTH, neTH :: Q Exp
eqTH = [| (==) |]
neTH = [| (/=) |]


-------------------------------------------------------------------------------
-- class (Ord a) (TODO missing ordering)
ltTH, geTH, gtTH, leTH, maxTH, minTH :: Q Exp
ltTH = [| (<) |]
geTH = [| (>=) |]
gtTH = [| (>) |]
leTH = [| (<=) |]
maxTH = [| max |]
minTH = [| min |]


-------------------------------------------------------------------------------
-- class (Num a)

plusTH, timesTH, minusTH, negateTH, absTH, signumTH :: Q Exp
plusTH = [| (+) |]
timesTH = [| (*) |]
minusTH = [| (-) |]
negateTH = [| negate |]
absTH = [| abs |]
signumTH = [| signum |]

fromIntegerTH :: Q Exp
fromIntegerTH = [| fromInteger |]

-------------------------------------------------------------------------------
-- class (Enum a)
-- TODO

-------------------------------------------------------------------------------
-- class (Bounded a)

minBoundTH, maxBoundTH :: Q Exp
minBoundTH = [| minBound |]
maxBoundTH = [| maxBound |]


-------------------------------------------------------------------------------
-- class (Num a, Ord a) => Real a 
-- TODO

-------------------------------------------------------------------------------
-- class (Real a, Enum a) => Integral a
-- TODO

-------------------------------------------------------------------------------
-- class Num a => Fractional a

divideTH, recipTH, fromRationalTH :: Q Exp
divideTH = [| (/) |]
recipTH = [| recip |]
fromRationalTH = [| fromRational |]

-- Must provide a Lift instance for type Rational = Ratio Integer
instance Integral a => Lift (Ratio a) where
  lift = liftRatio

liftRatio :: Integral a => Ratio a -> Q Exp
liftRatio r = return $ InfixE (Just numE) opE (Just denomE)
  where
  	opE    = VarE $ mkName "Data.Ratio.%"
  	numE   = LitE $ IntegerL $ fromIntegral $ numerator r
  	denomE = LitE $ IntegerL $ fromIntegral $ denominator r


-------------------------------------------------------------------------------
-- class Fractional a => Floating a

piTH, expTH, sqrtTH, logTH, powTH, logBaseTH, sinTH, tanTH, cosTH, asinTH, atanTH, acosTH, sinhTH, tanhTH, coshTH, asinhTH, atanhTH, acoshTH :: Q Exp

piTH = [| pi |]
expTH = [| exp |]
sqrtTH = [| sqrt |]
logTH = [| log |]
powTH = [| (**) |]
logBaseTH = [| logBase |]
sinTH = [| sin |]
tanTH = [| tan |]
cosTH = [| cos |]
asinTH = [| asin |]
atanTH = [| atan |]
acosTH = [| acos |]
sinhTH = [| sinh |]
tanhTH = [| tanh |]
coshTH = [| cosh |]
asinhTH = [| asinh |]
atanhTH = [| atanh |]
acoshTH = [| acosh |]


-------------------------------------------------------------------------------
-- class (Real a, Fractional a) => RealFrac a
-- TODO


-------------------------------------------------------------------------------
-- class (RealFrac a, Floating a) => RealFloat a
-- TODO


subtractTH :: Q Exp
subtractTH = [| subtract |]

evenTH :: Q Exp
evenTH = [| even |]

oddTH :: Q Exp
oddTH = [| odd |]

powIntegralTH :: Q Exp
powIntegralTH = [| (^) |]

powFractionalTH :: Q Exp
powFractionalTH = [| (^^) |]




