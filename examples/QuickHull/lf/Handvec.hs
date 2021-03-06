{-# LANGUAGE MagicHash, BangPatterns, ParallelArrays, TypeOperators #-}

module Handvec ( hsplit_v, Point, Line )
where

import AboveAndFarthestLF

import Points2D.Types

import Data.Array.Parallel as PA
import Data.Array.Parallel.Base as B
import Data.Array.Parallel.PArray ()
import Data.Array.Parallel.PArray.PData
import Data.Array.Parallel.PArray.PDataInstances
import Data.Array.Parallel.PArray.ScalarInstances
import Data.Array.Parallel.Lifted.Closure
import Data.Array.Parallel.Prelude as P'
import Data.Array.Parallel.Prelude.Double as D
import Data.Array.Parallel.Unlifted as U
import GHC.Exts

import Debug.Trace as Debug

import Prelude as P


-- | Vectorised version of hsplit.
--
-- A closure containing the original scalar version and the lifted version.
hsplit_v :: PArray Point :-> Line :-> PArray Point
hsplit_v = closure2 hsplit_s hsplit_l
{-# NOINLINE hsplit_v #-}


-- | Scalar version of hsplit (unused).
hsplit_s :: PArray Point -> Line -> PArray Point
hsplit_s ps _ = ps
{-# NOINLINE hsplit_s #-}


-- | The heart of QuickHull.
--
-- Wrapper for lifted hsplit with the type expected by the vectoriser
-- (which we still go through to avoid hand vectorising 'HandvecWrp.quickHull'.
hsplit_l :: PArray (PArray Point) -> PArray Line -> PArray (PArray Point)
hsplit_l (PArray _ points_s) (PArray nLines# lines)
  = let result@(PNested segd _) = hsplit_l' nLines# points_s lines
        nsegs = U.lengthSegd segd                        -- should be 2
    in  PArray (un# nsegs) result
{-# INLINE hsplit_l #-}


-- | Actually the heart of QuickHull.
--
-- The extra argument is the lifting context (number of lines/segments).
hsplit_l' :: Int# -> PData (PArray Point) -> PData Line -> PData (PArray Point)
hsplit_l' nLines# (PNested segd _) _
  | Debug.traceEvent ("GANG[1/1] Issuing hsplit_l' " ++
                      "with " ++ show (I# nLines#) ++ " lines " ++
                      "and " ++ show (U.elementsSegd segd) ++ " points, " ++
                      "distributed as: " ++ show (U.toList $ U.lengthsSegd segd)) False = undefined
hsplit_l' 0# _ _ = PNested U.emptySegd (P_2 (PDouble U.empty) (PDouble U.empty))
hsplit_l' nLines# points_s                                  -- E.g.: nLines#: 6, npts >= 13
          lines@(P_2 (P_2 (PDouble line_x1s) (PDouble line_y1s))
                     (P_2 (PDouble line_x2s) (PDouble line_y2s)))
  = let ( (PNested aboveSegd (P_2 (PDouble above_xs) (PDouble above_ys))),
          (P_2 (PDouble max_xs) (PDouble max_ys)))
          = aboveAndFarthestP points_s lines

        -- For some of the lines there are no more points left (segment length 0).
        -- The recursion for these lines has finished and we'll treat them separately.
        (above_lens,_,_) = unpackSegd aboveSegd             -- Segd ( [4, 5, 0, 2, 2,  0]
                                                            --      , [0, 4, 9, 9, 11, 13]
                                                            --      , 13 )

        -- Empty segments emptySelctor (empty -> 1; otherwise -> 0)
        emptySel    = U.tagsToSel2                          -- Sel2 ( [0, 0, 1, 0, 0, 1]
                    $ U.map B.fromBool                      --      , [0, 1, 0, 2, 3, 1]
                    $ U.zipWith (P.==) above_lens           --      , 4, 2 )
                                       (U.replicate (I# nLines#) 0)
        emptyTags   = U.tagsSel2 emptySel                   -- [0, 0, 1, 0, 0, 1]

        --- *** First take care of the lines for which the recursion hasn't finished *** ---
        --- ***                                                                      *** ---

        -- Create segd for the points above those lines, which still have points above them.
        -- This is equivalent to removing all empty segments from 'aboveSegd'.
        purgedSegd = U.lengthsToSegd                        -- Segd ( [4, 5, 2, 2]
                   $ U.packByTag above_lens emptyTags 0     --      , [0, 4, 9, 11]
                                                            --      , 13 )
        (purged_lens, purged_ids, _) = unpackSegd purgedSegd

        emptyTags_r = U.replicate_s aboveSegd emptyTags     -- [0, 0, 0, 0,     -- 4
                                                            --  0, 0, 0, 0, 0,  -- 5
                                                            --                  -- 0
                                                            --  0, 0,           -- 2
                                                            --  0, 0]           -- 2
                                                            --                  -- 0

        -- WATCH OUT: Redundant packByTag. Basically remove all empty segments from 'aboveSegd',
        -- without touching the data arrays. I.e. data-wise purged_s = above_s
        purged_s@(PNested _ (P_2 (PDouble xs') (PDouble ys')))
                    = PNested purgedSegd (P_2 (PDouble above_xs) (PDouble above_ys))
        --          = PNested purgedSegd (P_2 (PDouble $ U.packByTag above_xs emptyTags_r 0)
        --                                    (PDouble $ U.packByTag above_ys emptyTags_r 0))

        --- *** Prepare segd to call hsplit anew *** ---
        --- ***                                  *** ---

        -- Number of non-empty segments
        nFilled     = U.elementsSel2_0 emptySel                   -- 4

        -- New segd with one element per non-empty segment of 'aboveSegd' (farthest point)
        filled1Segd = U.mkSegd (U.replicate nFilled 1)            -- Segd ( [1, 1, 1, 1]
                               (U.enumFromStepLen 0 1 nFilled)    --      , [0, 1, 3, 4]
                               nFilled                            --      , 4 )

        -- New segd with two elements per non-empty segment of 'aboveSegd'.
        -- Represents the fact that we make two new lines out one current out before making the
        -- recursive call. They share the point farthest from the old line.
        filled2Segd = filled1Segd `U.plusSegd` filled1Segd        -- Segd ( [2, 2, 2, 2]
                                                                  --      , [0, 2, 4, 8]
        (_,_,filled2_elts) = unpackSegd filled2Segd               --      , 8 )


        -- Replicate each non-empty segment twice
        dbl_lens    = U.replicate_s filled2Segd purged_lens       -- Segd ( [4, 4, 5, 5, 2, 2, 2, 2]
        dblSegd     = U.lengthsToSegd dbl_lens                    --      , [0, 4, 8,13,18,20,22,24]
        (_,_,dbl_elts) = unpackSegd dblSegd                       --      ,  26 )

        -- Find indices to take from the points array to make it adhere to the doubled dblSegd
        -- (vsegs to the rescue?)
        ids_to_take = U.enumFromStepLenEach
                           dbl_elts                               -- 26 (length hint)
                           (U.replicate_s filled2Segd purged_ids) -- [0, 0, 4, 4, 9, 9,11,11]
                           (U.replicate   filled2_elts 1)         -- [1, 1, 1, 1, 1, 1, 1, 1]
                           dbl_lens                               -- [4, 4, 5, 5, 2, 2, 2, 2]
        -- ids_to_take: [0,1,2,3, 0,1,2,3, 4,5,6,7,8, 4,5,6,7,8, 9,10, 9,10, 11,12, 11,12]

        -- Actually perform doubling of all segments.
        -- Each line now has two identical segments for the points above it.
        aboveDbl_s  = PNested dblSegd (P_2 (PDouble $ U.bpermute xs' ids_to_take)
                                           (PDouble $ U.bpermute ys' ids_to_take))


        -- Remove points corresponding to lines with no points above them
        fars@(P_2 (PDouble far_xs) (PDouble far_ys))
                    = P_2 (PDouble $ U.packByTag max_xs emptyTags 0)
                          (PDouble $ U.packByTag max_ys emptyTags 0)

        -- Find lines to and from the farthest points (i.e. [:(p1, pm), (pm, p2):] in the original code).
        -- Remember we are only dealing with lines for which there are still points above them.
        -- The use of segments here is a convenient way to interleave the old line starts, with the
        -- farthest points (also used as line starts in the next iteration).
        -- filled2Segd is not used directly and is merely a hint to segmented append.
        farLine_1s  = P_2 (PDouble $ U.append_s filled2Segd
                                                filled1Segd (U.packByTag line_x1s emptyTags 0)
                                                filled1Segd far_xs)

                          (PDouble $ U.append_s filled2Segd
                                                filled1Segd (U.packByTag line_y1s emptyTags 0)
                                                filled1Segd far_ys)

        -- Line ends are interleaved in a similar manner.
        farLine_2s  = P_2 (PDouble $ U.append_s filled2Segd
                                                filled1Segd far_xs
                                                filled1Segd (U.packByTag line_x2s emptyTags 0))

                          (PDouble $ U.append_s filled2Segd
                                                filled1Segd far_ys
                                                filled1Segd (U.packByTag line_y2s emptyTags 0))
        farLines    = P_2 farLine_1s farLine_2s             -- 8 lines in total

        -- Finally make recursive call to compute convex hull (for the list with points still above them)
        hull_s@(PNested hullSegd (P_2 (PDouble hull_xs) (PDouble hull_ys)))
                    = hsplit_l' (un# filled2_elts) aboveDbl_s farLines

        -- hsplit returns *only* line starts. In the example above we had 4 lines with points above them
        (hull_lens,_,_) = unpackSegd hullSegd               -- Segd: [ 2, 1, 2, 2, 1, 1, 2, 1 ]
                                                            --                    ^          ^
                                                            -- Lines with finished recursion each contribute
                                                            -- one pt to hull. They go where ^ points.

        --- *** Now deal with the empty segnments, i.e. lines which have no points above them *** ---
        --- *** and will thus form part of the convex hull                                    *** ---
        nEmpty      = U.elementsSel2_1 emptySel             -- 2 lines have no more points above them

        -- Prepare the final segd to hold both the lines that have no above points as well as the remainder
        -- of the convex hull returned by the recursive call.
        resultSegd  = U.lengthsToSegd                       -- Segd: [3, 4, 1, 2, 3, 1]
                    $ U.combine2 (U.tagsSel2 emptySel)      -- [0, 0, 1, 0, 0, 1] (actually emptyTags)
                                 (U.repSel2  emptySel)      -- Distribution across PEs
                                 (U.sum_s filled2Segd hull_lens) -- [3, 4, 2, 3]
                                 (U.replicate nEmpty 1)          -- [1, 1]

        resultSel   = U.tagsToSel2                          -- [0,0,0, 0,0,0,0, 1, 0,0, 0,0,0, 1]
                    $ (U.replicate_s resultSegd emptyTags)
        resultTags  = U.tagsSel2 resultSel                  -- As above
        resultRepsel= U.repSel2  resultSel                  -- Distribution across PEs

        -- Combine data returned from 'hsplit' and the starts of the lines we left alone.
        result_xs   = U.combine2 resultTags
                                 resultRepsel
                                 hull_xs
                                 (U.packByTag line_x1s emptyTags 1)
        result_ys   = U.combine2 resultTags
                                 resultRepsel
                                 hull_ys
                                 (U.packByTag line_y1s emptyTags 1)

    in  (PNested resultSegd (P_2 (PDouble result_xs) (PDouble result_ys)))
{-# INLINE hsplit_l' #-}


aboveAndFarthestP :: PData (PArray Point) -> PData Line -> (PData (PArray Point), PData Point)
aboveAndFarthestP (PNested segd (P_2 (PDouble xs) (PDouble ys)))
                  (P_2 (P_2 (PDouble x1s) (PDouble y1s))
                       (P_2 (PDouble x2s) (PDouble y2s)))
  = let lens = U.lengthsSegd segd
        (above_xs, above_ys, far_xs, far_ys, lens') = aboveAndFarthest xs ys x1s y1s x2s y2s lens
        segd' = U.lengthsToSegd lens'
    in  ( PNested segd' (P_2 (PDouble above_xs) (PDouble above_ys))
        , P_2 (PDouble far_xs) (PDouble far_ys) )
{-# INLINE aboveAndFarthestP #-}


unpackSegd :: Segd -> (Array Int, Array Int, Int)
unpackSegd segd = ( U.lengthsSegd  segd
                  , U.indicesSegd  segd
                  , U.elementsSegd segd )
{-# INLINE unpackSegd #-}


-- | Unbox an integer.
un# :: Int -> Int#
un# (I# i#) = i#
{-# INLINE un# #-}
