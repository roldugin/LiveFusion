{-# LANGUAGE GADTs #-}
module Data.LiveFusion.Fuse where

import Data.LiveFusion.AST
import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.LoopFunctions as Loop
import Data.LiveFusion.Sharing
import Data.LiveFusion.Scalar.HOAS as HOAS
import Data.LiveFusion.HsBackend.Prelude
import Data.LiveFusion.Types
import Data.LiveFusion.Util

import Data.Dynamic
import Data.List as List
import Data.Map as Map hiding ( map, filter )
import Data.Maybe
import Data.Typeable


fuse :: Typeable e => Map Unique (WrappedASG Unique) -> (ASG e Unique) -> Unique -> Loop
fuse env node uq = fuse' node uq
 where
  fuse' :: Typeable e => (ASG e Unique) -> Unique -> Loop

  -- TODO: Unique id argument is essentially threaded through, can we abstract?
  fuse' var@(VarG uq) _ = fuse' node uq
   where
    node = fromJust
         $ (getASTNode env uq) `asTypeOf` (Just var)

  fuse' (ManifestG vec) uq = manifestG uq vec

  fuse' (MapG f arr)    uq = mapG uq f arr_loop
   where
    arr_loop = fuse' arr uq  -- TODO: this uq means nothing

  fuse' (ZipWithG f arr brr) uq = zipWithG uq f arr_loop brr_loop
   where
    arr_loop = fuse' arr uq
    brr_loop = fuse' brr uq

  fuse' (FilterG p arr) uq = filterG uq p arr_loop
   where
    arr_loop = fuse' arr uq

  fuse' (ScanG f z arr) uq = scanG uq f z' arr_loop
   where
    arr_loop = fuse' arr uq
    z'       = getScalar z uq

  -- See comment [1] at the bottom of the file
  fuse' (Fold_sG f z segd dat) uq = fold_sG uq f z' segd_loop data_loop
   where
    data_loop = fuse' dat uq
    segd_loop = fuse' segd uq
    z'        = getScalar z uq

  fuse' (Scan_sG f z segd dat) uq = scan_sG uq f z' segd_loop data_loop
   where
    data_loop = fuse' dat uq
    segd_loop = fuse' segd uq
    z'        = getScalar z uq

  fuse' (Replicate_sG len segd arr) uq = undefined

  -- | We store scalars in AST/ASG however, we're not yet clever about computing them.
  --   For not we assume that any scalar AST could only be constructed using Scalar constructor
  getScalar :: (Typeable e, Elt e) => (ASG e Unique) -> Unique -> Term e
  getScalar var@(VarG uq) _ = getScalar ast uq
    where ast = fromJust
              $ (getASTNode env uq) `asTypeOf` (Just var)
  getScalar (ScalarG term) _ = term
  getScalar _ _ = error "getScalar: Failed scalar lookup. Make sure the scalar argument is constructed with Scalar AST constructor."


-------------------------------------------------------------------------------
-- * Individual combinators - Don't look!
-- TODO: Introduce monadic interface to Loop.

manifestG uq vec = loop
 where
  arrVar     = arrayVar uq   -- array variable 'arr_uq'
  ixVar      = indexVar uq   -- index variable 'ix_uq'
  lenVar     = lengthVar uq  -- length variable 'len_uq'
  aVar       = eltVar uq     -- element variable 'elt_uq' (result of every read)

  -- init
  lenBind    = arrLenStmt lenVar arrVar
  init_stmts = [lenBind]

  -- body
  readStmt   = readArrStmt aVar arrVar (varE ixVar)  -- read statement
  body_stmts = [readStmt]

  -- labels
  init_      = initLbl uq
  body_      = bodyLbl uq

  -- THE loop
  loop       = addArg   arrVar (toDyn vec)
             $ addStmts init_stmts init_
             $ addStmts body_stmts body_
             $ addToInsertTests uq
             $ addToInsertIncrs uq
             $ setTheRate uq
             $ defaultLoop uq


mapG uq f arr_loop = loop
 where
  arr_uq     = getJustRate arr_loop

  aVar       = eltVar arr_uq         -- element of input array
  bVar       = eltVar uq             -- element of output array

  -- body
  fApp       = fun1 f aVar           -- f function application
  bBind      = bindStmt bVar fApp    -- bind result
  body_stmts = [bBind]               -- body block has two statements

  -- labels
  body_      = bodyLbl uq

  -- THE loop
  loop       = setTheRate uq
  	         $ setArrResultOnly uq
             $ addStmts body_stmts body_
             $ reuseRate                uq arr_uq
             $ rebindLengthVar          uq arr_uq
             $ addDefaultSynonymLabels  uq arr_uq
             $ setTheRate uq
             $ arr_loop


zipWithG uq f arr_loop brr_loop = loop
 where
  arr_uq    = getJustRate arr_loop
  brr_uq    = getJustRate brr_loop

  aVar      = eltVar arr_uq
  bVar      = eltVar brr_uq
  cVar      = eltVar uq

  -- body
  fApp       = fun2 f aVar bVar
  cBind      = bindStmt cVar fApp
  body_stmts = [cBind]

  -- labels
  body_      = bodyLbl uq

  -- THE loop
  loop       = setArrResultOnly uq
             $ addStmts body_stmts body_
             $ rebindLengthVar uq arr_uq -- be careful: arbitrary choice between a and b
             $ setTheRate uq
             $ abrr_loop

  -- First separately unite uq/arr_uq and uq/brr_uq
  -- so they know how to merge into one loop.
  arr_loop'  = reuseRate               uq arr_uq
  	         $ addDefaultSynonymLabels uq arr_uq
  	         $ arr_loop
  brr_loop'  = reuseRate               uq brr_uq
             $ addDefaultSynonymLabels uq brr_uq
             $ brr_loop
  abrr_loop  = arr_loop' `Loop.append` brr_loop'


filterG uq p arr_loop = loop
 where
  arr_uq     = getJustRate arr_loop
  aVar       = eltVar arr_uq
  bVar       = eltVar uq
  ixVar      = indexVar uq   -- writing index

  -- init
  ixInit     = bindStmt ixVar (LitE (0::Int))  -- index initialization
  init_stmts = [ixInit]

  -- body
  predExp    = fun1 p aVar
  guard      = guardStmt predExp bottom_
  bBind      = bindStmt bVar (VarE aVar)
  body_stmts = [guard, bBind]

  -- yield
  ixUpdate   = incStmt ixVar
  yield_stmts = [ixUpdate]

  -- labels
  init_      = initLbl uq
  body_      = bodyLbl uq
  yield_     = yieldLbl uq
  bottom_    = bottomLbl uq

  -- THE loop
  loop       = setArrResultOnly uq
             $ addStmts init_stmts  init_
             $ addStmts body_stmts  body_
             $ addStmts yield_stmts yield_
             -- Note that we aren't reusing the rate since read/write indexes are not synchronised
             $ freshRate       uq
             $ rebindLengthVar uq arr_uq
             $ addDefaultSynonymLabels uq arr_uq
             $ setTheRate uq
             $ arr_loop


scanG uq f z arr_loop = loop
 where
  arr_uq     = getJustRate arr_loop
  aVar       = eltVar arr_uq
  bVar       = eltVar uq
  zVar       = var "z" uq
  accVar     = var "acc" uq                -- accumulator

  -- init
  zBind      = bindStmt zVar (TermE z)
  accInit    = bindStmt accVar (VarE zVar) -- accumulator initialization
  init_stmts = [zBind, accInit]

  -- body
  bBind      = bindStmt bVar (VarE accVar)  -- resulting element is current accumulator
  body_stmts = [bBind]

  -- bottom
  fApp       = fun2 f accVar aVar
  accUpdate  = assignStmt accVar fApp
  bottom_stmts = [accUpdate]

  -- labels
  init_      = initLbl uq
  body_      = bodyLbl uq
  bottom_    = bottomLbl uq

  -- THE loop
  loop       = setTheRate uq
  	         $ setArrResult uq
  	         $ setScalarResult accVar
  	         $ addStmts init_stmts init_
             $ addStmts body_stmts body_
             $ addStmts bottom_stmts bottom_
             $ reuseRate                uq arr_uq
             $ rebindLengthVar          uq arr_uq
             $ addDefaultSynonymLabels  uq arr_uq
             $ setTheRate uq
             $ arr_loop


fold_sG uq f z segd_loop data_loop = loop
 where
  segd_uq   = getJustRate segd_loop
  data_uq   = getJustRate data_loop

  aVar      = eltVar data_uq           -- an element from data array

  -- init_segd (run once)
  zVar      = var "z" uq
  zBind     = bindStmt zVar (TermE z)              
  init_segd_stmts = [zBind]

  -- body_segd (run before each segment, and acts like init for the segment loop)
  accVar    = var "acc" uq                -- accumulator
  accReset  = bindStmt accVar (VarE zVar) -- accumulator initialisation
  body_segd_stmts = [accReset]

  -- NEW body_segd' separate from body_segd (run post inner loop)
  -- not much here besides the reassigning acc to elt
  -- but we did have to separate it from the previous body (segd_uq)
  bVar      = eltVar uq              -- an element of the result array
  bBind     = bindStmt bVar (VarE accVar)
  body_segd_stmts' = [bBind]

  -- bottom_data (run for each element)
  fApp      = fun2 f accVar aVar
  accUpdate = assignStmt accVar fApp
  bottom_data_stmts = [accUpdate]

  -- some label names
  init_segd   = initLbl segd_uq
  body_segd   = bodyLbl segd_uq
  body_segd'  = bodyLbl uq
  bottom_data = bottomLbl data_uq

  -- THE loop
  loop      = setTheRate uq
            $ setArrResult uq
            $ setScalarResult accVar
            -- Segd (segd_uq) stuff below
            $ addStmts init_segd_stmts init_segd
            $ addStmts body_segd_stmts body_segd
            $ addStmts body_segd_stmts' body_segd'
            -- Data (data_uq/uq) stuff below
            $ addStmts bottom_data_stmts bottom_data
            -- The usual stuff
            $ rebindLengthVar uq segd_uq
            $ nested_loops

  nested_loops = nestLoops segd_loop
                           data_loop
                           segd_uq   {- new rate: -}
                           uq        {- new id: -}


scan_sG uq f z segd_loop data_loop = loop
 where
  segd_uq   = getJustRate segd_loop
  data_uq   = getJustRate data_loop

  aVar      = eltVar data_uq           -- an element from data dataay

  -- init_segd (run once)
  zVar      = var "z" uq
  zBind     = bindStmt zVar (TermE z)              
  init_segd_stmts = [zBind]

  -- body_segd (run before each segment, and acts like init for the segment loop)
  accVar    = var "acc" uq                -- accumulator
  accReset  = bindStmt accVar (VarE zVar) -- accumulator initialisation
  body_segd_stmts = [accReset]

  -- body_data (run for each element)
  bVar      = eltVar uq
  bBind     = bindStmt bVar (VarE accVar) -- resulting element is current accumulator
  body_data_stmts = [bBind]

  -- bottom_data (run for each element)
  fApp      = fun2 f accVar aVar
  accUpdate = assignStmt accVar fApp
  bottom_data_stmts = [accUpdate]

  -- some label names
  init_segd   = initLbl segd_uq
  body_segd   = bodyLbl segd_uq
  body_data   = bodyLbl data_uq
  bottom_data = bottomLbl data_uq

  -- THE loop
  loop      = setArrResult uq
            $ setScalarResult accVar
            -- Segd (segd_uq) stuff below
            $ addStmts init_segd_stmts init_segd
            $ addStmts body_segd_stmts body_segd
            -- Data (data_uq/uq) stuff below
            $ addStmts body_data_stmts body_data
            $ addStmts bottom_data_stmts bottom_data
            -- The usual stuff
            $ rebindLengthVar uq data_uq
            $ nested_loops

  nested_loops = nestLoops segd_loop
                           data_loop
                           data_uq {- new rate: -}
                           uq      {- new id: -}


-- | Adds predefined control flow for nested loops.
--
-- The function takes loop/id of segd, loop/id of data,
-- id of rate (usually either segd_uq or data_uq) and id of result loop.
--
-- See comment [1] at the bottom of the file
nestLoops :: Loop -> Loop -> Unique -> Unique -> Loop
nestLoops segd_loop data_loop rate_uq new_uq = loop
 where
  segd_uq    = getJustRate segd_loop
  data_uq    = getJustRate data_loop

  -- body_segd (run before each segment, and acts like init for the segment loop)
  seglenVar  = eltVar segd_uq
  segendVar  = var "end" new_uq  -- element counter that is updated for every segment
  segendSet  = bindStmt segendVar (fun2 plusInt ixVar seglenVar)
  body_segd_stmts = [segendSet]

  -- guard_data
  ixVar      = indexVar data_uq
  grd        = guardStmt (fun2 ltInt ixVar segendVar) inner_loop_exit
  guard_data_stmts = [grd]
  
  -- labels
  init_      = initLbl new_uq
  guard_segd = guardLbl segd_uq
  body_segd  = bodyLbl segd_uq
  body_segd' = bodyLbl new_uq
  yield_segd = yieldLbl segd_uq
  guard_data = guardLbl data_uq

  inner_loop_exit
    | rate_uq == segd_uq = body_segd'
    | rate_uq == data_uq = yield_segd
    | otherwise = err_BAD_RATE

  -- THE loop
  loop = setTheRate new_uq
       $ reuseRate new_uq rate_uq
       -- Start with outer (segd) loop
       $ setFinalGoto init_ guard_segd
       -- Body of segd loop *before* going into inner loop
       $ addStmts body_segd_stmts body_segd
       $ setFinalGoto body_segd guard_data
       -- Replace statements in guard of data (assuming segd is correct)
       $ replaceStmts guard_data_stmts guard_data
       $ removeFromInsertTests data_uq
       $ loop'

  -- Unite the new loop with whatever loop provides the correct rate.
  loop'
    -- The new loop produces elements at the rate of segd
    | rate_uq == segd_uq
      -- Body of segd loop *after* coming back from inner loop
    = setFinalGoto body_segd' yield_segd
      -- Don't unite the body block! (see comment)
    $ addSynonymLabels (List.delete bodyNm stdLabelNames) new_uq segd_uq
    $ merged_loops
    -- The new loop produces elements at the rate of data
    | rate_uq == data_uq
    = addSynonymLabels stdLabelNames new_uq data_uq
    $ merged_loops
    -- Rate not recognised
    | otherwise = err_BAD_RATE

  merged_loops
    -- Note: Order of appending matters given the order of synonyms
    = Loop.append data_loop
    $ addSynonymLabel (initLbl data_uq) (initLbl segd_uq)
    $ addSynonymLabel (doneLbl data_uq) (doneLbl segd_uq)
    $ segd_loop

  err_BAD_RATE :: a
  err_BAD_RATE = error
               $ "nestLoops: Passed rate" +-+ show rate_uq +-+
                 "does not match segd" +-+ (paren $ show segd_uq) +-+
                 "or data" +-+ (paren $ show data_uq) +-+ "rates."


-- | Sets the upper bound of an array to be the same as that of another array.
--
-- Length propagates from first to last combinator in the pipeline.
--
-- 1st argument: curr
-- 2nd argument: prev
rebindLengthVar :: Unique -> Unique -> Loop -> Loop
rebindLengthVar curr prev = addStmt stmt (initLbl curr)
  where stmt = bindStmt (lengthVar curr) (VarE $ lengthVar prev)
