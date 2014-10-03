module Data.LiveFusion.Loop.Common where

import Data.Dynamic
import Data.Reify.Graph ( Unique )

type Name = String

type Id = Unique

type Arg = Dynamic

pprId :: Id -> String
pprId = show
