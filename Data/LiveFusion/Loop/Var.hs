module Data.LiveFusion.Loop.Var where

import Data.LiveFusion.Loop.Common


-------------------------------------------------------------------------------
-- * General

data Var = IdVar Name Id
         | SimplVar Name
  deriving ( Eq, Ord )

instance Show Var where
  show = pprVar


var :: Name -> Id -> Var
var = IdVar


pprName :: Name -> String
pprName = id


pprVar :: Var -> String
pprVar (IdVar name ident) = pprName name ++ "_" ++ pprId ident
pprVar (SimplVar name) = pprName name


-- Type classes for easier language tree traversal
class VarContainer c where
  mapVars :: (Var -> Var) -> c -> c


class Analyse construct where
  binds      :: construct -> [Var]
  references :: construct -> [Var]


-------------------------------------------------------------------------------
-- * Loop specific

eltVar :: Id -> Var
eltVar = var eltPrefix

indexVar :: Id -> Var
indexVar = var indexPrefix

lengthVar :: Id -> Var
lengthVar = var lengthPrefix

arrayVar :: Id -> Var
arrayVar = var arrayPrefix

resultVar :: Var
resultVar = SimplVar resultPrefix


eltPrefix    = "elt"
indexPrefix  = "ix"
lengthPrefix = "len"
arrayPrefix  = "arr"
resultPrefix = "result"
