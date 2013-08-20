{-# LANGUAGE GADTs #-}

-- | Loop is an abstract representation of a loop computation.
--   It can be used to generate loop code.

module Data.LiveFusion.Loop where

import Data.LiveFusion.Util

import Data.Map as Map hiding ( map )
import Data.Dynamic
import Data.List as List
import Data.Monoid

type Name  = String
type Arg   = Dynamic
type State = ( Var   -- Variable name
             , Expr  -- Initial value
             , Expr  -- Update at the end of each iteration
             )

-- A really ugly and error-prome loop representation
data Loop = Loop { -- | Global arguments and their values
                   args   :: (Map Var Arg)

                   -- | Mutable state
                 , state  :: [State]

                   -- | Loop-local binding
                 , binds  :: (Map Var Expr)

                   -- | Ordered guards (TODO: The Var is really a Label here)
                 , guards :: [(Expr,Var)]

                   -- | Minimal array length (TODO bad)
                 , len    :: Int
                 }


instance Show Loop where
  show (Loop args state binds guards len)
    = "Loop Args:   " ++ (show $ map pprVar $ Map.keys args) ++\
      "     State:  " ++ show state ++\
      "     Binds:  " ++ show binds  ++\
      "     Guards: " ++ show guards


addArg var arg loop = loop { args = args' }
  where args' = Map.insert var arg (args loop)


addState var init update loop = loop { state = state' }
  where state' = (var,init,update):(state loop)


addBind var expr loop = loop { binds = binds' }
  where binds' = Map.insert var expr (binds loop)


-- Guard which causes the end of loop on failure (like break)
addExitGuard cond = addGuard cond (Var "done") -- TODO: add a common set of labels

-- Guard which skips iteration on failure (like continue)
addSkipGuard cond = addGuard cond (Var "skip")

-- A guard with the specified condition and the failure label
addGuard cond onfail loop = loop { guards = guards' }
  where guards' = (guards loop) `List.union` [(cond, onfail)] -- guards are ordered


setLen n loop = loop { len = len' }
  where curr  = len loop
        len'  | curr == 0  = n
              | otherwise = n `min` curr


instance Monoid Loop where
  mempty = Loop Map.empty [] Map.empty [] 0
  mappend loop1 loop2
    = Loop { args   = args   `joinBy` Map.union
           , state  = state  `joinBy` List.union
           , binds  = binds  `joinBy` Map.union
           , guards = guards `joinBy` List.union
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


data Var = Var Name
  deriving ( Show, Eq, Ord )


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
data Expr where
  VarE   :: Var -> Expr
  App1   :: Var -> Var -> Expr
  App2   :: Var -> Var -> Var -> Expr
  App3   :: Var -> Var -> Var -> Var -> Expr
  IntLit :: Int -> Expr
  deriving ( Show, Eq )


pprExpr :: Expr -> String
pprExpr (App1 f x)
    = pprVar f `space` pprVar x
pprExpr (App2 f x y)
    = pprVar f `space` pprVar x `space` pprVar y
pprExpr (App3 f x y z)
    = pprVar f `space` pprVar x `space`
      pprVar y `space` pprVar z
pprExpr (IntLit i) = show i


pprName :: Name -> String
pprName = id


pprVar :: Var -> String
pprVar (Var name) = pprName name


-- | Create a new variable from a the given one
prime :: Var -> Var
prime (Var name) = Var $ name ++ "'"