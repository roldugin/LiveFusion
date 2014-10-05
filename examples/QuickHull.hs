-- The heart of vectorised QuickHull.
-- Based on hand-vectorise version of QuickHull found in:
-- ghc/libraries/dph/dph-examples/examples/spectral/QuickHull/handvec/Handvec.hs
{-# LANGUAGE RebindableSyntax #-}
module QuickHull where

import Data.LiveFusion as LF

import Prelude as P hiding ( map, replicate, zip, zipWith, filter, fst, snd )



farAndAbove :: Term Int                      -- Number of lines
            -> Array Int                     -- Segd
            -> Array Double -> Array Double  -- Points
            -> Array Double -> Array Double  -- Line starts
            -> Array Double -> Array Double  -- Line ends
            -> (Array Double, Array Double,  -- Farthest points
                Array Double, Array Double,  -- Points above lines
                Array Int)                   -- New segd
farAndAbove npts segd xs ys x1s y1s x2s y2s
  = let -- Find distance-like measures between each point and its respective line.
        distances = calcCross npts segd xs ys x1s y1s x2s y2s

        -- Throw out all the points which are below the line (i.e. distance <= 0).
        (above_xs, above_ys, aboveSegd) = calcAbove npts segd xs ys distances

        -- Find points farthest from each line.
        (fars_xs, fars_ys) = calcFarthest npts segd xs ys distances
    in  (fars_xs, fars_ys, above_xs, above_ys, aboveSegd)



-- | Find (relative) distances of points from line.
--
-- Each point can be above (positive distance) or below (negative distance)
-- a line as looking from the center of the convex hull.
--
-- Corresponds to 'cross' in the original program:
-- > cross  = [: distance p line | p <- points :]
calcCross :: Term Int                      -- Number of points
          -> Array Int                     -- Segd
          -> Array Double -> Array Double  -- Points
          -> Array Double -> Array Double  -- Line starts
          -> Array Double -> Array Double  -- Line ends
          -> Array Double                  -- Relative distances from lines
calcCross npts segd xs ys x1s y1s x2s y2s
  = zipWith6 distance xs
                      ys
                      (replicate_s npts segd x1s)
                      (replicate_s npts segd y1s)
                      (replicate_s npts segd x2s)
                      (replicate_s npts segd y2s)
{-# INLINE calcCross #-}



-- | Calculate cross product between vectors formed between a point and
--   each of the two line ends.
--
-- I.e. |x1-xo|   |x2-xo|
--      |     | x |     | = (x1-xo)(y2-yo)-(y1-yo)(x2-xo)
--      |y1-yo|   |y2-yo|
--
-- Not changed from the original source version thanks to vectavoid
-- (except tuples are dissolved).
distance :: Term Double -> Term Double -- Point
         -> Term Double -> Term Double -- Line start
         -> Term Double -> Term Double -- Line end
         -> Term Double                -- Distance
distance xo yo x1 y1 x2 y2
  = (x1 - xo) * (y2 - yo) - (y1 - yo) * (x2 - xo)



-- | Find points above the lines given distance-like measures.
--
-- Corresponds to 'packed' in the original program:
-- > packed = [: p | (p,c) <- zipP points cross, c D.> 0.0 :]
calcAbove :: Term Int                      -- Number of points
          -> Array Int                     -- Segd
          -> Array Double -> Array Double  -- Points
          -> Array Double                  -- Distances
          -> (Array Double, Array Double,  -- Points with positive distances
              Array Int                 )  -- New Segd
calcAbove npts segd xs ys distances
  = let -- Compute emptySelctor for positive elements ((>0) -> 1; otherwise -> 0)
        aboveTags  = zipWith (>.) distances (replicate npts 0.0)

        -- Compute segd for just the positive elements
        aboveSegd = count_s true segd aboveTags

        -- Get the actual points corresponding to positive elements
        above_xs  = packByBoolTag true aboveTags xs
        above_ys  = packByBoolTag true aboveTags ys

    in  (above_xs, above_ys, aboveSegd)
{-# INLINE calcAbove #-}



-- | For each line find a point farthest from that line.
--
-- Each segment is a collection of points above a certain line.
-- The array of Doubles gives (relative) distances of points from the line.
--
-- Corresponds to 'pm' in the original program:
-- > pm = points !: maxIndexP cross
calcFarthest :: Term Int                      -- Number of points
             -> Array Int                     -- Segment descriptor
             -> Array Double -> Array Double  -- Points
             -> Array Double                  -- Distances
             -> (Array Double, Array Double)  -- Points with biggest distances
calcFarthest npts segd xs ys distances
  = let -- Index the distances array, and find the indices corresponding to the
        -- largest distance in each segment
        indexed  = zip (indices_s npts segd)
                       distances
        max_ids  = fsts
                 $ fold_s maxSnd (0 .*. small) segd indexed

        small    = -999999

        -- Find indices to take from the points array by offsetting from segment starts
        ids      = zipWith (+) (indicesSegd segd)
                                max_ids
        max_xs   = bpermute xs ids
        max_ys   = bpermute ys ids

        -- We are only interested in the ones which are above the line
        -- (thus from segments containing points above line).
    in (max_xs, max_ys)
{-# INLINE calcFarthest #-}



indicesSegd :: Array Int -> Array Int
indicesSegd = scan (+) 0



-- | Find pair with the biggest second element.
maxSnd :: (Elt a, Elt b, IsOrd b) => Term (a, b) -> Term (a, b) -> Term (a, b)
maxSnd ab1 ab2 = let b1 = snd ab1
                     b2 = snd ab2
                 in  if b1 >=. b2 then ab1
                 	              else ab2
{-# INLINE maxSnd #-}
