{-# LANGUAGE TemplateHaskell #-}
module Data.LiveFusion.HSBackend where

import Data.LiveFusion.HSBackend.THDefinitions

import Language.Haskell.TH as TH
import System.IO.Unsafe ( unsafePerformIO )

data Impl a = Impl 
  {  hs :: a
  ,  th :: Maybe (Q TH.Exp)
  }


instance Show (Impl a) where
  show (Impl _ (Just f_th)) = pprint $ unsafePerformIO $ runQ f_th
  show (Impl hs Nothing) = "<value>"


nofuse_pureImpl :: a -> Impl a
nofuse_pureImpl f = (defaultImpl f)


defaultImpl :: a -> Impl a
defaultImpl f = Impl { hs = f, th = Nothing } 


plusImpl, timesImpl, minusImpl :: Num a => Impl (a -> a -> a)
plusImpl = Impl { hs = $plusTH, th = Just plusTH }
timesImpl = Impl { hs = $timesTH, th = Just timesTH }
minusImpl = Impl { hs = $minusTH, th = Just minusTH }

negateImpl, absImpl, signumImpl :: Num a => Impl (a -> a)
negateImpl = Impl $negateTH (Just negateTH)
absImpl = Impl $absTH (Just absTH)
signumImpl = Impl $signumTH (Just signumTH)