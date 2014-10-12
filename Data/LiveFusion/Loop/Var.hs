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

eltVar, indexVar, lengthVar, arrayVar :: Id -> Var
eltVar     = var eltPrefix
indexVar   = var indexPrefix
lengthVar  = var lengthPrefix
arrayVar   = var arrayPrefix

resultVar :: Var
resultVar  = SimplVar resultPrefix


eltPrefix, indexPrefix, lengthPrefix, arrayPrefix, resultPrefix :: Name
eltPrefix     = "elt"
indexPrefix   = "ix"
lengthPrefix  = "len"
arrayPrefix   = "arr"
resultPrefix  = "result"
