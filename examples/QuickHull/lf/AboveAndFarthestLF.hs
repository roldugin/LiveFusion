module AboveAndFarthestLF where

import Plugin

import Data.Vector.Unboxed as V

aboveAndFarthest :: Vector Double -> Vector Double  -- Points
                 -> Vector Double -> Vector Double  -- Line starts
                 -> Vector Double -> Vector Double  -- Line ends
                 -> Vector Int                      -- Segment descriptor
                 -> ( Vector Double, Vector Double  -- Points above lines
                 	, Vector Double, Vector Double  -- Points farthest from lines
                 	, Vector Int )                  -- New segment descriptor

aboveAndFarthest xs ys x1s y1s x2s y2s lens = (above_xs, above_ys, far_xs, far_ys, lens')
  where
  	((((above_xs, above_ys), far_xs), far_ys), lens') = run xs ys lens x1s y1s x2s y2s xs ys n n n n n n
  	n = V.length xs
{-# NOINLINE aboveAndFarthest #-}
