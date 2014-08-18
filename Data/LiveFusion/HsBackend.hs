{-# LANGUAGE TemplateHaskell, ViewPatterns #-}
module Data.LiveFusion.HsBackend where

import Data.LiveFusion.HsBackend.THDefinitions
import Data.LiveFusion.HsBackend.Types
import Data.LiveFusion.Backend

import Language.Haskell.TH as TH
import System.IO.Unsafe ( unsafePerformIO )
import Control.Monad

data Impl t = Impl
  {  hs :: t
  ,  th :: Maybe (Q TH.Exp)
  }

class (Code code) => (HsCode code) where
  getTH :: code t -> Maybe (Q TH.Exp)


unsafePprHsCode :: HsCode code => code t -> String
unsafePprHsCode (getTH -> Just qexp) = TH.pprint $ unsafePerformIO $ runQ qexp
unsafePprHsCode (getTH -> Nothing)   = "undefined"
{-# NOINLINE unsafePprHsCode #-}


instance HsCode Impl where
  getTH = th

instance Code Impl where
  getNative = hs

applyImpl :: Impl (a -> b) -> Impl a -> Impl b
applyImpl i1 i2 = Impl hs' th'
  where
    hs' = (hs i1) (hs i2)
    -- Note that application currently only works if there is TH code
    -- for both the function and the argument.
    th' = liftM2 TH.appE (th i1) (th i2)


instance Show (Impl a) where
  show (Impl _ (Just f_th)) = pprint $ unsafePerformIO $ runQ f_th
  show (Impl hs Nothing) = "<value>"


nofuse_pureImpl :: a -> Impl a
nofuse_pureImpl f = (defaultImpl f)


defaultImpl :: a -> Impl a
defaultImpl f = Impl { hs = f, th = Nothing } 


-------------------------------------------------------------------------------
-- Prelude --------------------------------------------------------------------
-- TODO this stuff should really be hidden somewhere is HaBackend hierarchy

-- Num ------------------------------------------------------------------------

plusImpl, timesImpl, minusImpl :: Num a => Impl (a -> a -> a)
plusImpl = Impl { hs = $plusTH, th = Just plusTH }
timesImpl = Impl { hs = $timesTH, th = Just timesTH }
minusImpl = Impl { hs = $minusTH, th = Just minusTH }

negateImpl, absImpl, signumImpl :: Num a => Impl (a -> a)
negateImpl = Impl $negateTH (Just negateTH)
absImpl = Impl $absTH (Just absTH)
signumImpl = Impl $signumTH (Just signumTH)

fromIntegerImpl :: Num a => Integer -> Impl a
fromIntegerImpl n = Impl (($fromIntegerTH) n) (Just [| $fromIntegerTH n |])


-- Eq -------------------------------------------------------------------------

eqImpl, neImpl :: Eq a => Impl (a -> a -> Bool)
eqImpl = Impl { hs = $eqTH, th = Just eqTH }
neImpl = Impl { hs = $neTH, th = Just neTH }


-- Ord ------------------------------------------------------------------------

ltImpl, leImpl, gtImpl, geImpl :: Ord a => Impl (a -> a -> Bool)
ltImpl = Impl { hs = $ltTH, th = Just ltTH }
leImpl = Impl { hs = $leTH, th = Just leTH }
gtImpl = Impl { hs = $gtTH, th = Just gtTH }
geImpl = Impl { hs = $geTH, th = Just geTH }

minImpl, maxImpl :: Ord a => Impl (a -> a -> a)
minImpl = Impl { hs = $minTH, th = Just minTH }
maxImpl = Impl { hs = $maxTH, th = Just maxTH }
