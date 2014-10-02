-- Copyright (c) [2013] Manuel M T Chakravarty.  All rights reserved.

{-# LANGUAGE GADTs, StandaloneDeriving, DeriveDataTypeable, NoMonomorphismRestriction, CPP #-}

module Data.LiveFusion.Scalar.HOAS where

import Data.LiveFusion.Backend
-- TODO: For now hardcode Haskell backend in. Abstract over any backend later.
import Data.LiveFusion.HsBackend.Impl

import Data.Typeable
import Text.Show.Functions


-- The level of lambda-bound variables. The root has level 0; then it increases with each bound
-- variable — i.e., it is the same as the size of the environment at the defining occurence.
--
type Level = Int

-- Lambda terms in higher-order abstract syntax
--
-- * We don't care about exotic terms here, and hence don't use a parametrised representation.
-- * The `Typeable' contexts and the `Tag' variant are in preparation for being able to convert to a
--   de Bruijn representation.
--
data Term t where
    -- for conversion to de Bruijn
  Tag :: Typeable t                                 => Level                   -> Term t    

  -- | Backend specific implementation of Term of type t
  CodeT :: (HsCode code, Typeable t, Show t)        => code t                  -> Term t
  Con   :: (Typeable t, Show t)                     => t                       -> Term t
  Lam   :: (Typeable s, Typeable t, Show s, Show t) => (Term s -> Term t)      -> Term (s -> t)
  App   :: (Typeable s, Typeable t, Show s, Show t) => Term (s -> t) -> Term s -> Term t

#if __GLASGOW_HASKELL__ < 708
deriving instance Typeable1 Term
#else
deriving instance Typeable Term
#endif

showTermOp :: Term t -> String
showTermOp (Tag lvl) = "Tag " ++ show lvl
showTermOp (CodeT code) = "Code "
showTermOp (Con v)   = "Con " ++ show v
showTermOp (Lam {})  = "Lam"
showTermOp (App {})  = "App"

instance Show (Term t) where
  show = showTermOp

-- Term constructors
--
code = CodeT
con = Con
lam = Lam
app = App

-- Additional helper constructors
--
lam2 f = lam $ \x -> lam $ \y -> f x y
lam3 f = lam $ \x -> lam $ \y -> lam $ \z -> f x y z
lam4 f = lam $ \x -> lam $ \y -> lam $ \z -> lam $ \w -> f x y z w
lam5 f = lam $ \x -> lam $ \y -> lam $ \z -> lam $ \w -> lam $ \v -> f x y z w v
lam6 f = lam $ \x -> lam $ \y -> lam $ \z -> lam $ \w -> lam $ \v -> lam $ \u -> f x y z w v u

-- A term interpreter for closed terms
--
intp :: Show t => Term t -> t
intp (Tag ix)      = error "HOAS.intp: Tag is only for conversion"
intp (CodeT code)  = getNative code
intp (Con v)       = v
intp (Lam fun)     = intp . fun . Con
intp (App fun arg) = (intp fun) (intp arg)
