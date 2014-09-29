module Data.LiveFusion.LoopFunctions where

import Data.LiveFusion.DisjointSet as Rates
import Data.LiveFusion.Loop as Loop

import Data.Reify.Graph ( Unique )


-- | Sets the index of the *previous* combinator in a pipeline to be the same
--   as the index of the current combinator, effectively making the rates equal.
--
-- Rate changing combinators like @filter@ should use @newRate@ function.
reuseRate :: Unique -> Unique -> Loop -> Loop
reuseRate new old loop = loop { loopRates = unionInsert new old (loopRates loop) }

freshRate :: Unique -> Loop -> Loop
freshRate rate loop = loop { loopRates = insert rate (loopRates loop) }

