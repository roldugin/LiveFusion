{-# LANGUAGE GADTs #-}

-- | Loop is an abstract representation of a loop computation.
--   It can be used to generate loop code.

module Data.LiveFusion.Loop where

import Data.LiveFusion.Util

import Data.Map as Map hiding ( map )
import Data.Reify ( Unique ) -- TODO remove coupling with data-reify
import Data.Dynamic
import Data.List as List
import Data.Monoid

type Name = Unique
type Arg  = Dynamic


-- A really ugly and error-prome loop representation
data Loop = Loop { args   :: (Map Name Arg)  {- Arguments -}
                 , binds  :: (Map Name Expr) {- Bindings -}
                 , guards :: [Expr]          {- Ordered guards -}
                 , arrs   :: [Name]          {- Arrays to iterate -}
                 , len    :: Int             {- Minimum array length -} -- TODO not a great way to do it
                 }


instance Show Loop where
  show (Loop args binds guards arrs len)
    = "Loop Args:   " ++ (show $ map (pprVarArg . ArgE) $ Map.keys args) ++\
      "     Binds:  " ++ show binds  ++\
      "     Guards: " ++ show guards ++\
      "     Arrs:   " ++ (show $ map (pprVarArg . VarE) $ arrs)


addArg name arg loop = loop { args = args' }
  where args' = Map.insert name arg (args loop)


addBind name expr loop = loop { binds = binds' }
  where binds' = Map.insert name expr (binds loop)


addGuard expr loop = loop { guards = guards' }
  where guards' = expr:(guards loop)


addVec name loop = loop { arrs = arrs' }
  where arrs' = name:(arrs loop)


setLen n loop = loop { len = len' }
  where curr  = len loop
        len'  | curr == 0  = n
              | otherwise = n `min` curr


instance Monoid Loop where
  mempty = Loop Map.empty Map.empty [] [] 0
  mappend loop1 loop2
    = Loop { args   = args   `joinBy` Map.union
           , binds  = binds  `joinBy` Map.union
           , guards = guards `joinBy` (++)
           , arrs   = arrs   `joinBy` List.union
           , len    = len    `joinBy` min
           }
    where
      joinBy :: (Loop  -> field)
             -> (field -> field -> field)
             -> field
      field `joinBy` f = f (field loop1) (field loop2)


append :: Loop -> Loop -> Loop
append = mappend


empty :: Loop
empty = mempty


data VarArg where
  VarE :: Name -> VarArg
  ArgE :: Name -> VarArg
  deriving Show

data Expr where
  App1 :: VarArg -> VarArg -> Expr
  App2 :: VarArg -> VarArg -> VarArg -> Expr
  deriving Show


pprVarArg :: VarArg -> String
pprVarArg (VarE n) = "var" ++ show n
pprVarArg (ArgE n) = "arg" ++ show n


pprExpr :: Expr -> String
pprExpr (App1 f x)   = pprVarArg f `space` pprVarArg x
pprExpr (App2 f x y) = pprVarArg f `space` pprVarArg x
                                   `space` pprVarArg y


-- TODO these two should go as soon as we stop passing Names around
-- and pass VarArgs directly
pprVar :: Name -> String
pprVar = pprVarArg . VarE

pprArg :: Name -> String
pprArg = pprVarArg . ArgE


{- Typed variables, arguments and expressions
data VarArg e where
  VarE :: forall e . (Elt e) => Name -> VarArg e
  ArgE :: forall e . (Elt e) => Name -> VarArg e

data Expr e where
  App1 :: (Elt a, Elt b) => VarArg (a -> b) -> VarArg a -> Expr b
  App2 :: (Elt a, Elt b, Elt c) => VarArg (a -> b -> c) -> VarArg a -> VarArg b -> Expr c
-}
