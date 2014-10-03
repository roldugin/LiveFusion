{-# LANGUAGE GADTs #-}
module Data.LiveFusion.Loop.Expr where

import Data.LiveFusion.Loop.Var
import Data.LiveFusion.Loop.Common

import Data.LiveFusion.Scalar.HOAS as HOAS
import qualified Data.LiveFusion.Scalar.DeBruijn as DeBruijn
import qualified Data.LiveFusion.Scalar.Convert as DeBruijn
import Data.LiveFusion.Types
import Data.LiveFusion.Util

import Data.LiveFusion.HsBackend.Types -- Bad!!

import Data.List as List
import Data.Typeable


-- | Represents an expression in the loop.
--
--   NOTE: It would be difficult to type the expression tree as `Expr a'
--         as we would no longer be able to easily construct collections
--         of such expressions, e.g.:
--   > [Expr Int, Expr Double, Expr Double]
--
--   Thoughts:
--   1. One way to keep the types would be to keep a TypeRep inside each Var.
--
--   2. Alternatively we could minimise the use of data structures such as lists
--   and maps and instead keep more stuff in the tree itself.
--
--   3. Now that we have DeBruijn term language that we use for scalar
--      functions specified by the user, perhaps we do not need a separate Expr
--      language.
--
data Expr where
  VarE  :: Var                              -> Expr
  AppE  :: Expr -> Expr                     -> Expr
  TermE :: (Typeable t) => HOAS.Term t      -> Expr
  LitE  :: (THElt e, Elt e) => e            -> Expr

instance Show Expr where
  show = pprExpr


instance VarContainer Expr where
  mapVars f = go
   where
    go (VarE v) = VarE (f v)
    go (AppE e1 e2) = AppE (mapVars f e1) (mapVars f e2)
    go e_ = e_


instance Analyse Expr where
  binds _ = []
  references = go
   where
    go (VarE v) = [v]
    go (AppE e1 e2) = go e1 `List.union` go e2
    go _ = []


vAppE :: Var -> Var -> Expr
vAppE f x = AppE (varE f) (varE x)


varE :: Var -> Expr
varE = VarE


-- | Shorthand for applying a 1-argument function to a var.
fun1 :: (Elt a, Elt b) => (Term a -> Term b) -> Var -> Expr
fun1 f x = (TermE (lam f)) `AppE` (VarE x)


-- | Shorthand for applying a 2-argument function to a var.
fun2 :: (Elt a, Elt b, Elt c) => (Term a -> Term b -> Term c) -> Var -> Var -> Expr
fun2 f x y = (TermE (lam2 f)) `AppE` (VarE x) `AppE` (VarE y)


fun6 :: (Elt a, Elt b, Elt c, Elt d, Elt e, Elt f, Elt g)
     => (Term a -> Term b -> Term c -> Term d -> Term e -> Term f -> Term g)
     -> Var -> Var -> Var -> Var -> Var -> Var -> Expr
fun6 fun a b c d e f = foldl apply (TermE (lam6 fun)) [a,b,c,d,e,f]
  where 
    apply :: Expr -> Var -> Expr
    apply e v = e `AppE` (VarE v)


constE :: (THElt e, Elt e) => e -> Expr
constE = LitE


pprExpr :: Expr -> String
pprExpr (VarE v)
  = pprVar v
pprExpr (AppE f x)
  = (pprExpr f) `space` (pprExpr x)
pprExpr (TermE t)
  -- TODO: Convert should not be here.
  = paren $ DeBruijn.pprTerm $ DeBruijn.convert t
pprExpr (LitE i)
  = show i
