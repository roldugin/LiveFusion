module Data.LiveFusion.Loop.Var where

import Data.LiveFusion.Loop.Common


-------------------------------------------------------------------------------
-- * General

data Var = Var Name Id
  deriving ( Eq, Ord )

instance Show Var where
  show = pprVar


var :: Name -> Id -> Var
var = Var


pprVar :: Var -> String
pprVar (Var name ident) = pprName name ++ "_" ++ pprId ident


varId :: Var -> Id
varId (Var _ i) = i


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
resultVar  = Var resultPrefix 0


eltPrefix, indexPrefix, lengthPrefix, arrayPrefix, resultPrefix :: Name
eltPrefix     = "elt"
indexPrefix   = "ix"
lengthPrefix  = "len"
arrayPrefix   = "arr"
resultPrefix  = "result"


isArrayVar :: Var -> Bool
isArrayVar (Var nm _) = nm == arrayPrefix 
isArrayVar _            = False
