{-# LANGUAGE GADTs #-}
module Data.LiveFusion.Fuse where

import Data.LiveFusion.AST
import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.LoopFunctions as Loop
import Data.LiveFusion.Sharing
import Data.LiveFusion.Scalar.HOAS as HOAS
import Data.LiveFusion.HsBackend.Prelude
import Data.LiveFusion.Types

import Data.Dynamic
import Data.List as List
import Data.Map as Map hiding ( map, filter )
import Data.Maybe
import Data.Typeable


-- | Don't look!
--
-- TODO: Introduce monadic interface to Loop.
--       Split this function into ones taking care of individual combinators.
fuse :: Typeable e => Map Unique (WrappedASG Unique) -> (ASG e Unique) -> Unique -> (Loop, Unique)
fuse env = fuse'
 where
  fuse' :: Typeable e => (ASG e Unique) -> Unique -> (Loop, Unique)

  -- TODO: Unique id argument is essentially threaded through, can we abstract?
  fuse' var@(VarG uq) _ = fuse' ast uq
   where
    ast = fromJust
        $ (getASTNode env uq) `asTypeOf` (Just var)


  fuse' (ManifestG vec) uq = (loop,uq)
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
               $ defaultLoop uq


  fuse' (MapG f arr) uq = (loop,uq)
   where
    (arr_loop, arr_uq) = fuse' arr uq -- TODO: this uq means nothing
    aVar       = eltVar arr_uq         -- element of input array
    bVar       = eltVar uq             -- element of output array

    -- body
    fApp       = fun1 f aVar           -- f function application
    bBind      = bindStmt bVar fApp    -- bind result
    body_stmts = [bBind]               -- body block has two statements

    -- labels
    body_      = bodyLbl uq

    -- THE loop
    loop       = setArrResultOnly uq
               $ addStmts body_stmts body_
               $ rebindIndexAndLengthVars uq arr_uq
               $ addDefaultSynonymLabels  uq arr_uq
               $ arr_loop


  fuse' (ZipWithG f arr brr) uq = (loop,uq)
   where
    (arr_loop, arr_uq) = fuse' arr uq
    (brr_loop, brr_uq) = fuse' brr uq
    aVar      = eltVar arr_uq
    bVar      = eltVar brr_uq
    -- First separately unite uq/arr_uq and uq/brr_uq
    -- so they know how to merge into one loop.
    arr_loop' = addDefaultSynonymLabels uq arr_uq arr_loop
    brr_loop' = addDefaultSynonymLabels uq brr_uq brr_loop
    abrr_loop = arr_loop' `Loop.append` brr_loop'
    -- BODY
    -- Binding for `f`
    fVar      = var "f" uq            -- name of function to apply
    fBody     = TermE (lam2 f)        -- f's body in HOAS representation
    fBind     = bindStmt fVar fBody   -- f = <HOAS.Term>              
    cVar      = eltVar uq             -- resulting element variable
    fApp      = (varE fVar) `AppE` (varE aVar) `AppE` (varE bVar) -- function application
    cBind     = bindStmt cVar fApp    -- bind result
    bodyStmts = [fBind,cBind]
    -- LOOP
    loop      = setArrResultOnly uq
       -- >       $ addArg fVar (toDyn f)
              $ addStmts bodyStmts (bodyLbl uq)
              $ rebindIndexAndLengthVars uq arr_uq -- be careful: arbitrary choice between a and b
              -- $ addDefaultControlFlow uq
              $ abrr_loop


  fuse' (FilterG p arr) uq = (loop,uq)
   where
    (arr_loop, arr_uq) = fuse' arr uq
    aVar      = eltVar arr_uq
    -- INIT
    ixVar     = indexVar uq                     -- writing index
    ixInit    = bindStmt ixVar (LitE (0::Int))  -- index initialization
    initStmts = [ixInit]
    -- BODY
    predExp   = AppE (TermE (lam p)) (varE aVar)
    guard     = guardStmt predExp (bottomLbl uq)
    resVar    = eltVar uq
    resBind   = bindStmt resVar (VarE aVar)
    -- NOTE: This will bug out if there are more guards
    --       or anything else important in the remainder of the body
    bodyStmts = [guard, resBind]
    -- YIELD
    -- WARNING: Assignment statement preceeds the array write stmt (added in the postprocess step)
    --          It it fine with the current semantics as the unupdated index will be used,
    --          however this is error prone and may not be true with code gens other than HsCodeGen.
    ixUpdate  = assignStmt ixVar (AppE (AppE (varE plusFn) (varE ixVar)) (LitE (1::Int)))  -- index step
    yieldStmts = [ixUpdate]
    -- LOOP
    loop      = setArrResultOnly uq
              -- >$ addArg pVar (toDyn p)
              $ addStmts initStmts (initLbl uq)
              $ addStmts bodyStmts (bodyLbl uq)
              $ addStmts yieldStmts (yieldLbl uq)
              -- Note that we aren't rebinding index since read/write indexes are not the same with Filter
              $ rebindLengthVar uq arr_uq
              -- $ addDefaultControlFlow uq
              $ addDefaultSynonymLabels uq arr_uq
              $ arr_loop


  fuse' (ScanG f z arr) uq = (loop, uq)
   where
    (arr_loop, arr_uq) = fuse' arr uq
    aVar      = eltVar arr_uq
    -- INIT
    zVar      = var "z" uq
    zBind     = bindStmt zVar (TermE $ getScalar z uq)
    accVar    = var "acc" uq                -- accumulator
    accInit   = bindStmt accVar (VarE zVar) -- accumulator initialization
    initStmts = [zBind, accInit]
    -- BODY
    bVar      = eltVar uq
    bBind     = bindStmt bVar (VarE accVar) -- resulting element is current accumulator
    bodyStmts = [bBind]
    -- BOTTOM
    -- Binding for `f`
    fVar      = var "f" uq            -- name of function to apply
    fBody     = TermE (lam2 f)        -- f's body in HOAS representation
    fBind     = bindStmt fVar fBody   -- f = <HOAS.Term>  
    fApp      = (varE fVar) `AppE` (varE accVar) `AppE` (varE aVar)
    accUpdate = assignStmt accVar fApp
    botStmts  = [fBind, accUpdate]
    -- LOOP
    loop      = setArrResult uq
              $ setScalarResult accVar
              -- $ addArg zVar (toDyn z)
              $ addStmts initStmts (initLbl uq)
              $ addStmts bodyStmts (bodyLbl uq)
              $ addStmts botStmts  (bottomLbl uq)
              $ rebindIndexAndLengthVars uq arr_uq
              -- $ addDefaultControlFlow uq
              $ addDefaultSynonymLabels uq arr_uq
              $ arr_loop

  -- See comment [1] at the bottom of the file
  fuse' (Fold_sG f z segd arr) uq = (loop, uq)
   where
    (data_loop, data_uq) = fuse' arr uq
    aVar      = eltVar data_uq           -- an element from data array
    (segd_loop, segd_uq) = fuse' segd uq

    -- init_segd (run once)
    zVar      = var "z" uq
    zBind     = bindStmt zVar (TermE $ getScalar z uq)              
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
    loop      = setArrResult uq
              $ setScalarResult accVar
              -- Segd (segd_uq) stuff below
              $ addStmts init_segd_stmts init_segd
              $ addStmts body_segd_stmts body_segd
              $ addStmts body_segd_stmts' body_segd'
              -- Data (data_uq/uq) stuff below
              $ addStmts bottom_data_stmts bottom_data
              -- The usual stuff
              $ rebindIndexAndLengthVars uq segd_uq
              $ nested_loops

    nested_loops = nestLoops (segd_loop,segd_uq)
                             (data_loop,data_uq)
                             segd_uq {- new rate: -}
                             uq      {- new id: -}


  fuse' (Scan_sG f z segd dat) uq = (loop, uq)
   where
    (data_loop, data_uq) = fuse' dat uq
    aVar      = eltVar data_uq           -- an element from data dataay

    (segd_loop, segd_uq) = fuse' segd uq

    -- init_segd (run once)
    zVar      = var "z" uq
    zBind     = bindStmt zVar (TermE $ getScalar z uq)              
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
              $ rebindIndexAndLengthVars uq data_uq
              $ nested_loops

    nested_loops = nestLoops (segd_loop,segd_uq)
                             (data_loop,data_uq)
                             data_uq {- new rate: -}
                             uq      {- new id: -}


  fuse' (Replicate_sG len segd arr) uq = undefined


  -- | We store scalars in AST/ASG however, we're not yet clever about computing them.
  --   For not we assume that any scalar AST could only be constructed using Scalar constructor
  getScalar :: (Typeable e, Elt e) => (ASG e Unique) -> Unique -> Term e
  getScalar var@(VarG uq) _ = getScalar ast uq
    where ast = fromJust
              $ (getASTNode env uq) `asTypeOf` (Just var)
  getScalar (ScalarG term) _ = term
  getScalar _ _ = error "getScalar: Failed scalar lookup. Make sure the scalar argument is constructed with Scalar AST constructor."


-- | Adds predefined control flow for nested loops.
--
-- The function takes loop/id of segd, loop/id of data,
-- id of rate (usually either segd_uq or data_uq) and id of result loop.
--
-- See comment [1] at the bottom of the file
nestLoops :: (Loop,Unique) -> (Loop,Unique) -> Unique -> Unique -> Loop
nestLoops (segd_loop, segd_uq) (data_loop, data_uq) rate_uq new_uq = loop
 where
  -- body_segd (run before each segment, and acts like init for the segment loop)
  seglenVar = eltVar segd_uq
  segendVar = var "end" new_uq  -- element counter that is updated for every segment
  segendSet = bindStmt segendVar (fun2 plusInt ixVar seglenVar)
  body_segd_stmts = [segendSet]

  -- guard_data
  ixVar = indexVar data_uq
  lt = (<.) :: Term Int -> Term Int -> Term Bool
  grd = guardStmt (fun2 lt ixVar segendVar) body_segd'
  guard_data_stmts = [grd]
  
  -- some label redefinitions
  init_      = initLbl new_uq

  guard_segd = guardLbl segd_uq
  body_segd  = bodyLbl segd_uq
  body_segd' = bodyLbl new_uq

  yield_segd = yieldLbl segd_uq
  guard_data = guardLbl data_uq

  -- THE loop
  loop = id
       -- Start with outer (segd) loop
       $ setFinalGoto init_ guard_segd
       -- Body of segd loop *before* going into inner loop
       $ addStmts body_segd_stmts body_segd
       $ setFinalGoto body_segd guard_data
       -- Replace statements in guard of data (assuming segd is correct)
       $ replaceStmts guard_data_stmts guard_data
       $ loop'

  -- Unite the new loop with whatever loop provides the correct rate.
  loop'= case rate_uq of
          -- If the new loop produces elements at the rate of segd
          segd_uq ->
            -- Body of segd loop *after* coming back from inner loop
            setFinalGoto body_segd' yield_segd
            -- Don't unite the body block! (see comment)
            $ addSynonymLabels (List.delete bodyNm stdLabelNames) new_uq segd_uq
            $ merged_loops

          -- If the new loop produces elements at the rate of data
          data_uq ->
            addSynonymLabels stdLabelNames new_uq data_uq
            $ merged_loops

  merged_loops
       -- Note: Order of appending matters given the order of synonyms
       = Loop.append data_loop
       $ addSynonymLabel (initLbl data_uq) (initLbl segd_uq)
       $ addSynonymLabel (doneLbl data_uq) (doneLbl segd_uq)
       $ segd_loop




-- | Sets the upper bound of an array to be the same as that of another array.
--
-- Length propagates from first to last combinator in the pipeline.
--
-- 1st argument: curr
-- 2nd argument: prev
rebindLengthVar :: Unique -> Unique -> Loop -> Loop
rebindLengthVar curr prev = addStmt stmt (initLbl curr)
  where stmt = bindStmt (lengthVar curr) (VarE $ lengthVar prev)


-- | See comments for @rebind{Index,Length}Var@,
--   especially the direction of propagation.
--
-- 1st argument: curr
-- 2nd argument: prev
rebindIndexAndLengthVars :: Unique -> Unique -> Loop -> Loop
rebindIndexAndLengthVars curr prev = rebindLengthVar curr prev
                                   . reuseRate       curr prev
