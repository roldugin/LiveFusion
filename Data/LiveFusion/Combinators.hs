{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes,
             FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators, NamedFieldPuns, LambdaCase, ExplicitForAll #-}
module Data.LiveFusion.Combinators where

import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.Util
import Data.LiveFusion.HsEvaluator
import Data.LiveFusion.Types
import Data.LiveFusion.Scalar.HOAS as HOAS

-- For testing
import Data.LiveFusion.HsBackend.Prelude
import Data.LiveFusion.HsCodeGen

import qualified Data.Vector.Unboxed as V
import Prelude hiding ( map, zip, filter, zipWith )
import qualified Prelude as P
import Unsafe.Coerce
import GHC.Prim (Any)
import qualified Data.List as P
import Data.Typeable
import GHC hiding ( Unique, pprExpr ) -- TODO instead import what's needed
import GHC.Paths -- ( libdir )
import DynFlags -- ( defaultFatalMessager, defaultFlushOut )
import Control.Exception
import Debug.Trace
import System.IO
import System.IO.Unsafe
import System.FilePath
import Data.Reify
import Data.Reify.Graph
import Data.Map as Map hiding ( map, filter )
import Control.Applicative
import Text.Show.Functions
import Data.Maybe
import Data.List as List
import Data.Dynamic
import Control.Arrow ( (>>>) )
import Language.Haskell.TH ( pprint )


tr a = trace (show a) a

uc = unsafeCoerce

ucText = "unsafeCoerce"


type ScalarAST a = AST a
type ArrayAST a = AST (V.Vector a)


-- | Abstract Syntax Tree whose nodes represent delayed collective array operations.
data AST e where
  Map      :: (Elt a, Elt b)
           => (Term a -> Term b)
           -> ArrayAST a
           -> ArrayAST b

  Filter   :: Elt a
           => (Term a -> Term Bool)
           -> ArrayAST a
           -> ArrayAST a

  ZipWith  :: (Elt a, Elt b, Elt c)
           => (Term a -> Term b -> Term c)
           -> ArrayAST a
           -> ArrayAST b
           -> ArrayAST c

  Zip      :: (Elt a, Elt b)
           => ArrayAST a
           -> ArrayAST b
           -> ArrayAST (a,b)

  Fold     :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST a
           -> ScalarAST a

  Scan     :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST a
           -> ArrayAST a

  Fold_s   :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST Int
           -> ArrayAST a
           -> ArrayAST a

  Scan_s   :: Elt a
           => (Term a -> Term a -> Term a)
           -> ScalarAST a
           -> ArrayAST Int
           -> ArrayAST a
           -> ArrayAST a

  Replicate_s
           :: Elt a
           => Int
           -> ArrayAST Int
           -> ArrayAST a
           -> ArrayAST a

  Manifest :: Elt a
           => V.Vector a
           -> ArrayAST a

  Scalar   :: Elt a
           => Term a
           -> ScalarAST a


-- Required for getting data-reify to work with GADTs
data WrappedASG s where
  Wrap :: Typeable e => ASG e s -> WrappedASG s


deriving instance Show (WrappedASG Unique)


type ScalarASG a s = ASG a s
type ArrayASG a s = ASG (V.Vector a) s

-- The following fails for 2+ argument functions
--type family Fun t where
--  Fun (a -> b) = HOAS.Term a -> HOAS.Term b
--  Fun a = HOAS.Term a


-- | Abstract Semantic Graph is a directed acyclic graph derived from the AST
--   of delayed collective array operations by:
--   * Replacing every point of recursion with a uniquely named variable
--   * Eliminating common subexpressions and representing them as one node, reference by
--     variables of the same name.
data ASG e s where
  MapG      :: (Elt a, Elt b)
            => (Term a -> Term b)
            -> ArrayASG a s
            -> ArrayASG b s

  FilterG   :: Elt a
            => (Term a -> Term Bool)
            -> ArrayASG a s
            -> ArrayASG a s

  ZipWithG  :: (Elt a, Elt b, Elt c)
            => (Term a -> Term b -> Term c)
            -> ArrayASG a s
            -> ArrayASG b s
            -> ArrayASG c s

  ZipG      :: (Elt a, Elt b)
            => ArrayASG a s
            -> ArrayASG b s
            -> ArrayASG (a,b) s

  FoldG     :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG a s
            -> ScalarASG a s

  ScanG     :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG a s
            -> ArrayASG a s

  ManifestG :: Elt a
            => V.Vector a
            -> ArrayASG a s

  ScalarG   :: Elt a
            => Term a
            -> ScalarASG a s

  Fold_sG   :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG Int s
            -> ArrayASG a s
            -> ArrayASG a s

  Scan_sG   :: Elt a
            => (Term a -> Term a -> Term a)
            -> ScalarASG a s
            -> ArrayASG Int s
            -> ArrayASG a s
            -> ArrayASG a s

  Replicate_sG
            :: Elt a
            => Int
            -> ArrayASG Int s
            -> ArrayASG a s
            -> ArrayASG a s

  VarG      :: Typeable e
            => s
            -> ASG e s


deriving instance Show s => Show (ASG e s)
deriving instance Typeable ASG


instance Typeable e => MuRef (AST e) where
  type DeRef (AST e) = WrappedASG
  mapDeRef ap e = Wrap <$> mapDeRef' ap e
    where
      mapDeRef' :: Applicative ap
                => (forall b. (MuRef b, WrappedASG ~ DeRef b) => b -> ap u)
                -> AST e
                -> ap (ASG e u)

      mapDeRef' ap (Map f arr)
        = MapG f
          <$> (VarG <$> ap arr)

      mapDeRef' ap (Filter p arr)
        = FilterG p
          <$> (VarG <$> ap arr)

      mapDeRef' ap (ZipWith f arr brr)
        = ZipWithG f
          <$> (VarG <$> ap arr)
          <*> (VarG <$> ap brr)

      mapDeRef' ap (Zip arr brr)
        = ZipG
          <$> (VarG <$> ap arr)
          <*> (VarG <$> ap brr)

      mapDeRef' ap (Fold f z arr)
        = FoldG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Scan f z arr)
        = ScanG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Fold_s f z lens arr)
        = Fold_sG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap lens)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Scan_s f z segd arr)
        = Scan_sG f
          <$> (VarG <$> ap z)
          <*> (VarG <$> ap segd)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Replicate_s len segd arr)
        = Replicate_sG len
          <$> (VarG <$> ap segd)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Manifest vec)
        = pure $ ManifestG vec

      mapDeRef' ap (Scalar x)
        = pure $ ScalarG x


getASTNode :: Typeable e => Map Unique (WrappedASG Unique) -> Unique -> Maybe (ASG e Unique)
getASTNode m n = case m ! n of Wrap  e -> cast e


recoverSharing :: Typeable e => AST e -> IO (Map Unique (WrappedASG Unique), Unique, Maybe (ASG e Unique))
recoverSharing e = do
  Graph l n <- reifyGraph e
  let m = Map.fromList l
  return (m, n, getASTNode m n)
{-# NOINLINE recoverSharing #-}


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
    arrVar    = arrayVar uq   -- array variable 'arr_uq'
    ixVar     = indexVar uq   -- index variable 'ix_uq'
    lenVar    = lengthVar uq  -- length variable 'len_uq'
    aVar      = eltVar uq     -- element variable 'elt_uq' (result of every read)

    -- init
    lenBind   = bindStmt lenVar (AppE (varE lengthFn) (varE arrVar))
    init_stmts = [lenBind]

    -- body
    readStmt  = readArrStmt aVar arrVar (varE ixVar)  -- read statement
    body_stmts = [readStmt]

    -- labels
    init_     = initLbl uq
    body_     = bodyLbl uq

    -- THE loop
    loop      = addArg   arrVar (toDyn vec)
              $ addStmts init_stmts init_
              $ addStmts body_stmts body_
              $ defaultLoop uq


  fuse' (MapG f arr) uq = (loop,uq)
   where
    (arr_loop, arr_uq) = fuse' arr uq -- TODO: this uq means nothing
    aVar      = eltVar arr_uq         -- element of source array
    -- BODY
    -- Binding for `f`
    fVar      = var "f" uq            -- name of function to apply
    fBody     = TermE (lam f)         -- f's body in HOAS representation
    fBind     = bindStmt fVar fBody   -- f = <HOAS.Term>
    -- Binding for result element `b`
    bVar      = eltVar uq             -- resulting element variable
    fApp      = AppE (varE fVar) (varE aVar) -- function application
    bBind     = bindStmt bVar fApp    -- bind result
    bodyStmts = [fBind, bBind]        -- body block has two statements
    -- LOOP
    loop      = setArrResultOnly uq
              -- >$ addArg fVar (toDyn f)
              $ addStmts bodyStmts (bodyLbl uq)
              $ rebindIndexAndLengthVars uq arr_uq
              -- $ addDefaultControlFlow uq
              $ addDefaultSynonymLabels uq arr_uq
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


fun2 :: (Elt a, Elt b, Elt c) => (Term a -> Term b -> Term c) -> Var -> Var -> Expr
fun2 f x y = (TermE (lam2 f)) `AppE` (VarE x) `AppE` (VarE y)


-- | Add sequential loop statements to an existing loop.
--
-- Given a unique 'uq' of a loop it will insert the following statements:
-- @
--   guard:
--     unless ix_uq < len_uq | done_uq
--   bottom:
--     ix_uq := ix_uq + 1
-- @
iterate :: Unique -> Loop -> Loop
iterate uq = addStmt indexTest guard
           . addStmt indexInc  bottom
  where
    ix     = indexVar uq
    len    = lengthVar uq

    indexTest = guardStmt (fun2 ltInt ix len) done
    indexInc  = incStmt ix

    guard  = guardLbl uq
    bottom = bottomLbl uq
    done   = doneLbl uq


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




-- | Sets the upper bound of an array to be the same as that
--   of another array.
rebindLengthVar :: Unique -> Unique -> Loop -> Loop
rebindLengthVar nu old = addStmt stmt (initLbl nu)
  where stmt = bindStmt (lengthVar nu) (VarE $ lengthVar old)

-- | Sets the index of a combinator to be the same as that of
--   the previous combinator in a pipeline.
--   
--   Since the index is likely to change it updates it in the guard.
rebindIndexVar :: Unique -> Unique -> Loop -> Loop
rebindIndexVar nu old = addStmt bndStmt (yieldLbl nu)
                      . addStmt bndStmt (doneLbl nu)
  where bndStmt = bindStmt (indexVar nu) (VarE $ indexVar old)


rebindIndexAndLengthVars :: Unique -> Unique -> Loop -> Loop
rebindIndexAndLengthVars nu old = rebindLengthVar nu old
                                . rebindIndexVar nu old


fuseToLoop :: Typeable e => AST e -> IO Loop
fuseToLoop ast = do
  (env, rootUq, Just rootNode) <- recoverSharing ast
  let (loop, resultUq) = fuse env rootNode rootUq
  return loop


resultType :: t a -> a
resultType _ = undefined


instance (Typeable e, Show e) => Show (AST e) where
  show = show . evalAST

showAST :: AST e -> String
showAST (Map _ arr) = "Map (" P.++ (showAST arr) P.++ ")"
showAST (Filter _ arr) = "Filter (" P.++ (showAST arr) P.++ ")"
showAST (ZipWith _ arr brr) = "ZipWith (" P.++ (showAST arr) P.++ ") (" P.++ (showAST brr) P.++ ")"
showAST (Zip arr brr) = "Zip (" P.++ (showAST arr) P.++ ") (" P.++ (showAST brr) P.++ ")"
showAST (Fold _ _ arr) = "Fold (" P.++ (showAST arr) P.++ ")"
showAST (Manifest vec) = show vec



eval :: Elt a => ArrayAST a -> V.Vector a
eval (Manifest vec) = vec
eval op = evalAST op

evalAST :: Typeable a => AST a -> a
evalAST ast = result
  where
    loop = getLoop ast
    dynResult = evalLoop loop (typeOf result)
    result = fromJust $ fromDynamic dynResult
{-# NOINLINE evalAST #-}

getLoop :: Typeable a => AST a -> Loop
getLoop = postprocessLoop . unsafePerformIO . fuseToLoop
{-# NOINLINE getLoop #-}

-------------- Tests -------------------------


-- | Prints code for an AST with line numbers to stdout.
justIndexedCode :: Typeable e => AST e -> IO ()
justIndexedCode ast = putStrLn $ indexed $ defaultPluginCode (getLoop ast) (tyArgTy ast)


-- | Prints code for an AST to stdout.
justCode :: Typeable e => AST e -> IO ()
justCode ast = putStrLn $ defaultPluginCode (getLoop ast) (tyArgTy ast)


-- | Gets TypeRep of a type arguments.
--
-- Example:
-- > tyArgTy (AST (Vector Int))
-- Vector Int
tyArgTy :: forall t a . Typeable a => t a -> TypeRep
tyArgTy _ = typeOf (undefined :: a)


--example0 :: ArrayAST Int
--example0 = ZipWith (+)
--       (fl [1,2,3])
--      $ Scan (+) 0 $ Filter (const True) $ Map (+1) $ fl [4,5,6]

--test0 :: IO ()
--test0 = print $ eval example0

--example1 :: ArrayAST Int
--example1 = Map (+1) $ Map (*2) (fl [1,2,3])

--test1 :: IO ()
--test1 = print $ eval example1

--example2 :: ArrayAST Int
--example2 = ZipWith (*) (Map (+1) $ fl [1,2,3,4,5,6,7,8]) (ZipWith (+) (fl $ take 20 [-8,-7..]) (Map (\x->x*2+1) $ fl [1..8]))

--test2 :: IO ()
--test2 = print $ eval example2


{-
runTests = do
  let runTest = print . eval
  mapM_ runTest [ test1, testMap1, testFilt1, testZipWith1, testMapG
                , testZipWithG, {- testZip1, -} testShare, testManyMaps]
  runTest testMZW

test1 :: ArrayAST Int
test1 = zipWith (*) (map (+1) $ fl [1,2,3,4,5,6,7,8]) (zipWith (+) (filter (<0) $ fl $ take 20 [-8,-7..]) (map (\x->x*2+1) $ fl [1..8]))

testMap1 :: ArrayAST Int
testMap1 = map (\x->x*2+1) $ fl [1..8]

testFilt1 :: ArrayAST Int
testFilt1 = filter (<0) $ fl $ take 20 [-8,-7..]

testZipWith1 :: ArrayAST Int
testZipWith1 = zipWith (+) testMap1 testFilt1

testMapG :: ArrayAST Int
testMapG = map (+1) $ fl [1,2,3,4,5,6,7,8]

testZipWithG :: ArrayAST Int
testZipWithG = zipWith (*) testMapG testZipWith1

testZip1 :: ArrayAST Int
testZip1 = map (uncurry (*)) $ zip testMapG testZipWith1

testShare :: ArrayAST Int
testShare = zipWith (+) (map (+1) arr) (map (+2) arr)
  where arr = fl [1,2,3]

testManyMaps :: ArrayAST Int
testManyMaps = map (+1) $ map (+2) $ map (+3) $ fl [1,2,3]

testMZW :: ArrayAST (Int,Double)
testMZW = zipWith k (zipWith g xs fys) (zipWith h fys zs)
  where k = (\l r -> (l+r,1.0))
        g = (*)
        h = max
        f = (+1)
        fys = map f ys
        xs = fl [1,2,3]
        ys = fl [4,5,6]
        zs = fl [7,8,9]
-}

{- [1]
fold_s and other reductions run at the rate of the segment descriptor.
This means they result in one element per segment.
Thus the yielding loop is the outer one.
So we could do
@
body_segd:
  elt_segd = ...
  goto guard_data
guard_data:
  unless ... goto yield_segd
@

The problem is that there may be more combinators consuming the output of fold_s, e.g.:

@ map f $ fold_s f z segd arr @

The `map` will insert its body statements into the `body_segd`
where the result of folding a segment is not yet available.

One possible solution is to have a new `body_segd'` block
which will be entered after each segment is complete:
@
body_segd:
  elt_segd = ...
  goto guard_data
guard_data:
  unless ix < segend | goto body_segd'
body_segd':
  ...
@
This could actually be the general solution for all combinators
but we will only apply it to segmented combinators with segd output rates for now.
-}
