{-# LANGUAGE MultiParamTypeClasses, GADTs, FlexibleContexts, StandaloneDeriving, TemplateHaskell, KindSignatures, RankNTypes #-}
module Data.LiveFusion.Types where

import qualified Data.Vector.Unboxed as V
import Data.Typeable
import Data.Word

class (Show a, V.Unbox a, Typeable a) => Elt a

instance Elt Int
instance Elt Float
instance Elt Double
instance Elt Bool
instance Elt Word8
instance (Elt a, Elt b) => Elt (a,b)
instance (Elt a, Elt b, Elt c) => Elt (a,b,c)
instance (Elt a, Elt b, Elt c, Elt d) => Elt (a,b,c,d)
