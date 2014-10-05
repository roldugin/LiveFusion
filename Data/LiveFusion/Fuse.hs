{-# LANGUAGE GADTs #-}
module Data.LiveFusion.Fuse where

import Data.LiveFusion.AST
import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.Sharing
import Data.LiveFusion.Scalar.HOAS as HOAS
import Data.LiveFusion.HsBackend.Prelude
import Data.LiveFusion.Types
import Data.LiveFusion.Util

import Data.Dynamic
import Data.List as List
import Data.Map as Map hiding ( map, filter, foldr )
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

  fuse' (ZipWith6G f arr brr crr drr err frr) uq
    = zipWith6G uq f arr_loop brr_loop crr_loop drr_loop err_loop frr_loop
   where
    arr_loop = fuse' arr uq
    brr_loop = fuse' brr uq
    crr_loop = fuse' crr uq
    drr_loop = fuse' drr uq
    err_loop = fuse' err uq
    frr_loop = fuse' frr uq

  fuse' (FilterG p arr) uq = filterG uq p arr_loop
   where
    arr_loop = fuse' arr uq

  fuse' (ScanG f z arr) uq = scanG uq f z' arr_loop
   where
    arr_loop = fuse' arr uq
    z'       = getScalar z uq

  fuse' (ReplicateG n x) uq = replicateG uq n x

  fuse' (BpermuteG arr ixs) uq = bpermuteG uq arr_loop ixs_loop
   where
    arr_loop = fuse' arr uq
    ixs_loop = fuse' ixs uq

  fuse' (PackByBoolTagG tag tags arr) uq = packByBoolTagG uq tag tags_loop arr_loop
   where
    tags_loop = fuse' tags uq
    arr_loop  = fuse' arr uq

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

  fuse' (Replicate_sG len segd dat) uq = replicate_sG uq len segd_loop data_loop
   where
   	data_loop = fuse' dat uq
   	segd_loop = fuse' segd uq

  fuse' (Indices_sG len segd) uq = indices_sG uq len segd_loop
   where
   	segd_loop = fuse' segd uq


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
  loop       = setArrResultOnly uq
  	         $ addArg   arrVar (toDyn vec)
             $ addStmts init_stmts init_
             $ addStmts body_stmts body_
             $ producerLoop uq


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

  abrr_loop  = mergeLoops uq [arr_loop, brr_loop]


zipWith6G uq f al bl cl dl el fl = loop
 where
  e loop     = eltVar $ getJustRate loop    -- to get eltVar of a loop
  a_uq       = getJustRate al

  -- body
  fApp       = fun6 f (e al) (e bl) (e cl) (e dl) (e el) (e fl)
  gVar       = eltVar uq
  gBind      = bindStmt gVar fApp
  body_stmts = [gBind]

  -- labels
  body_      = bodyLbl uq

  -- THE loop
  loop       = setArrResultOnly uq
             $ addStmts body_stmts body_
             $ rebindLengthVar uq a_uq -- be careferul!
             $ setTheRate uq
             $ afrr_loop

  afrr_loop  = mergeLoops uq [al, bl, cl, dl, el, fl]


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
             $ addToSkipTests uq
             $ addToSkipIncrs uq
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


-- | A combination of zipWith and filter.
packByBoolTagG uq tag tags_loop arr_loop = loop
 where
  arr_uq     = getJustRate arr_loop
  tags_uq    = getJustRate tags_loop
  tagVar     = eltVar tags_uq
  aVar       = eltVar arr_uq
  bVar       = eltVar uq
  ixVar      = indexVar uq   -- writing index

  -- init
  ixInit     = bindStmt ixVar (LitE (0::Int))  -- index initialization
  init_stmts = [ixInit]

  -- body
  predExp    = fun1 (==. tag) tagVar
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
             $ addToSkipTests uq
             $ addToSkipIncrs uq
             -- Do not merge with the new rate, because we are filtering
             $ mergeLoops arr_uq [arr_loop, tags_loop]


fold_sG uq f z segd_loop data_loop = loop
 where
  segd_uq   = getJustRate segd_loop
  data_uq   = getJustRate data_loop

  aVar      = eltVar data_uq           -- an element from data array

  -- init_segd (run once)
  zVar      = var "z" uq
  zBind     = bindStmt zVar (TermE z)              
  init_segd_stmts = [zBind]

  -- nest_segd (run before each segment, and acts like init for the segment loop)
  accVar    = var "acc" uq                -- accumulator
  accReset  = bindStmt accVar (VarE zVar) -- accumulator initialisation
  nest_segd_stmts = [accReset]

  bVar      = eltVar uq              -- an element of the result array
  bBind     = bindStmt bVar (VarE accVar)
  body_segd_stmts = [bBind]

  -- bottom_data (run for each element)
  fApp      = fun2 f accVar aVar
  accUpdate = assignStmt accVar fApp
  bottom_data_stmts = [accUpdate]

  -- some label names
  init_segd   = initLbl segd_uq
  nest_segd   = nestLbl segd_uq
  body_segd   = bodyLbl segd_uq
  bottom_data = bottomLbl data_uq

  -- THE loop
  loop      = setTheRate uq
            $ setArrResult uq
            $ setScalarResult accVar
            -- Segd (segd_uq) stuff below
            $ addStmts init_segd_stmts init_segd
            $ addStmts nest_segd_stmts nest_segd
            $ addStmts body_segd_stmts body_segd
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

  aVar      = eltVar data_uq           -- an element from data array

  -- init_segd (run once)
  zVar      = var "z" uq
  zBind     = bindStmt zVar (TermE z)              
  init_segd_stmts = [zBind]

  -- nest_segd (run before each segment, and acts like init for the segment loop)
  accVar    = var "acc" uq                -- accumulator
  accReset  = bindStmt accVar (VarE zVar) -- accumulator initialisation
  nest_segd_stmts = [accReset]

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
  nest_segd   = nestLbl segd_uq
  body_data   = bodyLbl data_uq
  bottom_data = bottomLbl data_uq

  -- THE loop
  loop      = setArrResult uq
            $ setScalarResult accVar
            -- Segd (segd_uq) stuff below
            $ addStmts init_segd_stmts init_segd
            $ addStmts nest_segd_stmts nest_segd
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


-- | Both segd_loop and elts_loop run at the rate of segd.
--   The resulting result_loop is an entirely new loop with a much higher rate.
--   This is why we rely on the length hint to allocate an array of the right size.
replicate_sG uq len segd_loop elts_loop = loop
 where
  segd_uq   = getJustRate segd_loop
  elts_uq   = getJustRate elts_loop
  result_uq = getJustRate result_loop

  -- init_result
  resLenVar = lengthVar result_uq    
  resLenBind= bindStmt resLenVar (TermE len)
  init_result_stmts = [resLenBind]

  -- body_result
  -- TODO: Check if optimised away. If not, move to body_source.
  aVar      = eltVar elts_uq
  bVar      = eltVar result_uq
  bBind     = bindStmt bVar (VarE aVar)
  body_result_stmts = [bBind]

  -- some label names
  nest_segd   = nestLbl segd_uq
  body_segd   = bodyLbl segd_uq
  init_result = initLbl result_uq
  body_result = bodyLbl result_uq

  -- THE loop
  loop      = setArrResultOnly uq
            $ addStmts init_result_stmts init_result
            $ addStmts body_result_stmts body_result
            -- aVar needs to be created before going into inner loop
            $ moveWithDeps aVar body_segd nest_segd
            $ nested_loops

  nested_loops = nestLoops source_loop
                           result_loop
                           result_uq {- new rate: -}
                           uq        {- new id: -}

  -- This is the loop that runs at the rate of output data
  result_loop = producerLoop uq

  -- Merge segd and element loops, make it have segd_uq rate
  source_loop = mergeLoops segd_uq [segd_loop, elts_loop]


indices_sG uq len segd_loop = loop
 where
  segd_uq   = getJustRate segd_loop
  result_uq = getJustRate result_loop

  bVar      = eltVar result_uq  -- result array variable

  -- init_result
  resLenVar = lengthVar result_uq    
  resLenBind= bindStmt resLenVar (TermE len)
  init_result_stmts = [resLenBind]

  -- nest_segd (reset index counter)
  bReset    = bindStmt bVar zeroE
  nest_segd_stmts = [bReset]

  -- bottom_result (increment counter)
  bIncr     = incStmt bVar
  bottom_result_stmts = [bIncr]

  -- some label names
  init_result   = initLbl result_uq
  bottom_result = bottomLbl result_uq
  nest_segd     = nestLbl segd_uq

  -- THE loop
  loop      = setArrResultOnly uq
            $ addStmts init_result_stmts init_result
            $ addStmts bottom_result_stmts bottom_result
            $ addStmts nest_segd_stmts nest_segd
            $ nested_loops

  nested_loops = nestLoops segd_loop
                           result_loop
                           result_uq {- new rate: -}
                           uq        {- new id: -}

  -- This is the loop that runs at the rate of output data
  result_loop = producerLoop uq


replicateG uq n x = loop
 where
  -- init_result
  lenVar     = lengthVar uq    
  lenBind    = bindStmt lenVar (TermE n)
  init_stmts = [lenBind]

  -- body_result
  xVar       = eltVar uq
  xBind      = bindStmt xVar (TermE x)
  body_stmts = [xBind]

  -- some label names
  init_ = initLbl uq
  body_ = bodyLbl uq

  -- THE loop
  loop      = setArrResultOnly uq
            $ addStmts init_stmts init_
            $ addStmts body_stmts body_
            $ producerLoop uq

bpermuteG uq arr_loop ixs_loop = loop
 where
  arr_uq     = getJustRate arr_loop
  ixs_uq     = getJustRate ixs_loop

  aVar       = eltVar arr_uq   -- element from data array
  aixVar     = indexVar arr_uq -- index at which data array is read
  ixVar      = eltVar ixs_uq   -- element from index array
  bVar       = eltVar uq       -- resulting element

  -- body (sets up the index to read from)
  ixBind     = bindStmt aixVar (varE ixVar)
  bBind      = bindStmt bVar   (varE aVar)   
  body_stmts = [ixBind,bBind]

  -- labels
  body_      = bodyLbl uq

  -- THE loop
  loop       = setArrResultOnly uq
  	         $ addStmts body_stmts body_
             $ setTheRate uq
             -- Arr has random access rate. No rate really.
             $ addToSkipIncrs arr_uq
             $ addToSkipTests arr_uq
             $ reuseRate uq ixs_uq
             $ rebindLengthVar uq ixs_uq
             -- Technically arr_loop is not a loop,
             -- safely merge it in.
             $ Loop.append ixs_loop
             $ addDefaultSynonymLabels ixs_uq uq
             $ addDefaultSynonymLabels uq arr_uq
             $ arr_loop


-- | Create a loop to be used by a produces.
--
-- Used by manifest, replicate, enum, etc..
producerLoop :: Unique -> Loop
producerLoop uq = id
                $ defaultLoop uq


-- | Merges a number of loops to run together in a lock-step.
--
-- Used by zipN, zipWithN, replicate_s, enum_s
mergeLoops :: Unique -> [Loop] -> Loop
mergeLoops _ []
  = error "mergeLoops: List of loops to merge must not be empty."
mergeLoops new_uq loops
  = setTheRate new_uq
  $ foldl1 Loop.append
  $ map prepare loops
  where
    -- First separately unite unite rates/labels with uq
    -- so they know how to merge into one loop.
    prepare loop
      = let loop_uq = getJustRate loop
        in  reuseRate                 new_uq loop_uq
  	        $ addDefaultSynonymLabels new_uq loop_uq
  	        $ loop


-- | Adds predefined control flow for nested loops.
--
-- The function takes segd_loop, data_loop,
-- id of rate (either segd_uq or data_uq) and id of result loop.
--
-- See comment [1] at the bottom of the file
nestLoops :: Loop -> Loop -> Unique -> Unique -> Loop
nestLoops segd_loop data_loop rate_uq new_uq = loop
 where
  segd_uq    = getJustRate segd_loop
  data_uq    = getJustRate data_loop

  -- labels
  init_segd  = initLbl segd_uq
  init_data  = initLbl data_uq
  done_segd  = doneLbl segd_uq
  done_data  = doneLbl data_uq

  -- THE loop
  loop = setTheRate new_uq
       $ reuseRate new_uq rate_uq
       $ addToSkipTests data_uq
       $ setNesting (segd_uq, data_uq)
       $ addDefaultSynonymLabels new_uq rate_uq
       $ Loop.append segd_loop
       $ addSynonymLabel init_segd init_data
       $ addSynonymLabel done_segd done_data
       $ data_loop


-- | Sets the upper bound of an array to be the same as that of another array.
--
-- Length propagates from first to last combinator in the pipeline.
--
-- 1st argument: curr
-- 2nd argument: prev
rebindLengthVar :: Unique -> Unique -> Loop -> Loop
rebindLengthVar curr prev = addStmt stmt (initLbl curr)
  where stmt = bindStmt (lengthVar curr) (VarE $ lengthVar prev)
