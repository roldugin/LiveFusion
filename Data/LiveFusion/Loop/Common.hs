module Data.LiveFusion.Loop.Common where

import Data.Dynamic
import qualified Data.Reify.Graph as Reify

type Name = String

type Unique = Reify.Unique

type Id = Unique

type Arg = Dynamic

pprId :: Id -> String
pprId = show
