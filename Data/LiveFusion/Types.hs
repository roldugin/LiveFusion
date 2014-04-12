{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleContexts, StandaloneDeriving, TemplateHaskell, KindSignatures, RankNTypes #-}
module Data.LiveFusion.Types
  ( module Data.LiveFusion.Types
	, module Data.LiveFusion.HSBackend
  ) where

import Data.LiveFusion.HSBackend
import Data.LiveFusion.Scalar.HOAS

import qualified Data.Vector.Unboxed as V
import Data.Typeable
import Data.Word
import Data.Maybe
--import Control.Applicative
import qualified Language.Haskell.TH as TH
import           Language.Haskell.TH ( Q )
import Prelude as P
import Text.Show.Functions


class (Show a, V.Unbox a, Typeable a) => Elt a

instance Elt Int
instance Elt Float
instance Elt Double
instance Elt Bool
instance Elt Word8
instance (Elt a, Elt b) => Elt (a,b)
instance (Elt a, Elt b, Elt c) => Elt (a,b,c)
instance (Elt a, Elt b, Elt c, Elt d) => Elt (a,b,c,d)


--data Exp t where
--  ConstE :: t -> Exp t
--  FunE   :: Impl t -> Exp t
--  AppE   :: Exp (a -> b) -> Exp a -> Exp b


--instance Show t => Show (Exp t) where
--  show (ConstE t) = show t
--  show (FunE impl) = show impl
--  show (AppE f x) = show f ++ " <>"


--instance Functor Exp where
--  fmap f x = FunE (nofuse_pureImpl f) <*> x
--instance Applicative Exp where
--  pure a = FunE (nofuse_pureImpl a)
--  f <*> x = AppE f x

-- | A lot like Applicative's <*>
--(<.>) :: Exp (a -> b) -> Exp a -> Exp b
--f <.> x = AppE f x


--getImpl :: Exp a -> Impl a
--getImpl (FunE impl) = impl
--getImpl (AppE f x) = applyImpl (getImpl f) (getImpl x)
--getImpl (ConstE x) = error "Constant expressions are not yet supported" -- TODO


-------------------------------------------------------------------------------
-- Prelude --------------------------------------------------------------------

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


