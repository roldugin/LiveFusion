module AboveAndFarthestLF where

import Plugin

import Data.Vector.Unboxed as V

import Timing

import Debug.Trace
import System.IO.Unsafe


-- | Set to true to print plugin's runtime at every iteration of the algorithm.
dEBUG_TIME :: Bool
dEBUG_TIME = False


aboveAndFarthest :: Vector Double -> Vector Double  -- Points
                 -> Vector Double -> Vector Double  -- Line starts
                 -> Vector Double -> Vector Double  -- Line ends
                 -> Vector Int                      -- Segment descriptor
                 -> ( Vector Double, Vector Double  -- Points above lines
                 	, Vector Double, Vector Double  -- Points farthest from lines
                 	, Vector Int )                  -- New segment descriptor

aboveAndFarthest xs ys x1s y1s x2s y2s lens = (above_xs, above_ys, far_xs, far_ys, lens')
  where
    force = xs `seq` ys `seq` lens `seq` x1s `seq` y1s `seq` x2s `seq` y2s `seq` ()

    ((((above_xs, above_ys), far_xs), far_ys), lens')
          = force `seq` showPureTime
          $ run xs ys lens x1s y1s x2s y2s xs ys n n n n n n

    n     = V.length xs
{-# NOINLINE aboveAndFarthest #-}


showPureTime :: a -> a
showPureTime p
  = if not dEBUG_TIME then p
	                  else unsafePerformIO $ do
    (v, t)
        <- time 
        $ let v	= p
          in  v `seq` return v

    putStr $ prettyTime t
    return v
{-# NOINLINE showPureTime #-}
