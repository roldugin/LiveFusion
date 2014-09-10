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

      mapDeRef' ap (Manifest vec)
        = pure $ ManifestG vec

      mapDeRef' ap (Scalar x)
        = pure $ ScalarG x

-- This is confusing at the moment: Var refers Unique that identifies the tree node we want to fetch
getASTNode :: Typeable e => Map Unique (WrappedASG Unique) -> Unique -> Maybe (ASG e Unique)
getASTNode m n = case m ! n of Wrap  e -> cast e

recoverSharing :: Typeable e => AST e -> IO (Map Unique (WrappedASG Unique), Unique, Maybe (ASG e Unique))
recoverSharing e = do
  Graph l n <- reifyGraph e
  let m = Map.fromList l
  return (m, n, getASTNode m n)
{-# NOINLINE recoverSharing #-}



fuse :: Typeable e => Map Unique (WrappedASG Unique) -> (ASG e Unique) -> Unique -> (Loop, Unique)
fuse env = fuse'
  where
    fuse' :: Typeable e => (ASG e Unique) -> Unique -> (Loop, Unique)
    -- TODO: Unique id argument is essentially threaded through, can we abstract?
    fuse' var@(VarG uq) _
        = let ast = fromJust
                  $ (getASTNode env uq) `asTypeOf` (Just var)
          in  fuse' ast uq

    fuse' (ManifestG vec) uq
        = let arrVar    = arrayVar uq

              -- INIT
              lenVar    = lengthVar uq
              lenBind   = bindStmt lenVar (AppE (varE lengthFn) (varE arrVar))
              ixVar     = indexVar uq                     -- index variable
              ixInit    = bindStmt ixVar (LitE (0::Int))  -- index initialization
              initStmts = [ixInit, lenBind]

              -- GUARD
              predE     = AppE (AppE (varE ltFn) (varE ixVar)) (varE lenVar) -- boolean guard predicate
              ixGuard   = guardStmt predE (doneLbl uq)
              grdStmts  = [ixGuard]

              -- BODY
              aVar      = eltVar uq                            -- result of every read
              aBind     = readArrStmt aVar arrVar (varE ixVar) -- read statement
              bodyStmts = [aBind]

              -- BOTTOM
              ixUpdate  = assignStmt ixVar ((varE plusFn) `AppE` (varE ixVar) `AppE` (LitE (1::Int)))
              botStmts  = [ixUpdate]

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg arrVar (toDyn vec)
                        $ addStmts initStmts  (initLbl uq)
                        $ addStmts grdStmts   (guardLbl uq)
                        $ addStmts bodyStmts  (bodyLbl uq)
                        $ addStmts botStmts   (bottomLbl uq)
                        $ addDefaultControlFlow uq
                        $ setLoopEntry (initLbl uq)
                        $ touchDefaultBlocks uq
                        $ Loop.empty
          in  (loop, uq) -- TODO return a result that maps an element of array

    fuse' (MapG f arr) uq
        = let (arr_loop, arr_uq) = fuse' arr uq -- TODO: this uq means nothing
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
          in  (loop, uq)

    fuse' (ZipWithG f arr brr) uq
        = let (arr_loop, arr_uq) = fuse' arr uq
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
          in  (loop, uq)

    fuse' (FilterG p arr) uq
        = let (arr_loop, arr_uq) = fuse' arr uq
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

              -- WRITE
              -- WARNING: Assignment statement preceeds the array write stmt (added in the postprocess step)
              --          It it fine with the current semantics as the unupdated index will be used,
              --          however this is error prone and may not be true with code gens other than HsCodeGen.
              ixUpdate  = assignStmt ixVar (AppE (AppE (varE plusFn) (varE ixVar)) (LitE (1::Int)))  -- index step
              writeStmts = [ixUpdate]

              -- LOOP
              loop      = setArrResultOnly uq
                        -- >$ addArg pVar (toDyn p)
                        $ addStmts initStmts (initLbl uq)
                        $ addStmts bodyStmts (bodyLbl uq)
                        $ addStmts writeStmts (writeLbl uq)
                        -- Note that we aren't rebinding index since read/write indexes are not the same with Filter
                        $ rebindLengthVar uq arr_uq
                        -- $ addDefaultControlFlow uq
                        $ addDefaultSynonymLabels uq arr_uq
                        $ arr_loop
          in  (loop, uq)

    fuse' (ScanG f z arr) uq
        = let (arr_loop, arr_uq) = fuse' arr uq
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
          in  (loop, uq)


    fuse' (Fold_sG f z lens arr) uq
        = let (arr_loop, arr_uq)   = fuse' arr uq
              (lens_loop, lens_uq) = fuse' lens uq
          in undefined


    fuse' (Scan_sG f z segd arr) uq
        = let (arr_loop, arr_uq)   = fuse' arr uq
              aVar      = eltVar arr_uq           -- an element from data array

              (segd_loop, segd_uq) = fuse' segd uq
              seglenVar = eltVar segd_uq          -- an element from segd array

              -- INIT_segd (run once)
              zVar      = var "z" uq
              zBind     = bindStmt zVar (TermE $ getScalar z uq)              
              initStmts_segd = [zBind]

              -- BODY_segd (run before each segment, and acts like init for the segment loop)
              jVar      = var "j" uq  -- element counter that resets with every segment
              jReset    = bindStmt jVar (LitE (0::Int))

              accVar    = var "acc" uq                -- accumulator
              accReset  = bindStmt accVar (VarE zVar) -- accumulator initialisation

              bodyStmts_segd = [jReset, accReset]
              segd2dataJump  = updateBlock (bodyLbl segd_uq)
                                           (setBlockFinal $ gotoStmt (guardLbl arr_uq))

              -- BOTTOM_segd (run after each segment)
              -- Nothing here

              -- DONE_segd
              linkDones = updateBlock (doneLbl segd_uq)
                                      (setBlockFinal $ gotoStmt (doneLbl arr_uq))

              -- INIT_data (run once)
              -- No new statements here but we do change the final statement to
              -- goto INIT_segd, so both loop are properly initialised
              linkInits = updateBlock (initLbl arr_uq)
                                      (setBlockFinal $ gotoStmt (initLbl segd_uq))

              -- GUARD_data (run for each element)
              -- Check if we reached the end of segment
              segendPred= (varE ltFn) `AppE` (varE jVar) `AppE` (varE seglenVar)
              jGuard    = guardStmt segendPred (writeLbl segd_uq) -- jump out of the loop into segd loop
              grdStmts_data = [jGuard]
              -- TODO
              -- The guard of block of data loop already has a guard with goto doneLbl_data.
              -- However, the preexisting guard is redundant (assuming segd is correct)
              -- We may want to replace current guards with new ones


              -- BODY_data (run for each element)
              bVar      = eltVar uq
              bBind     = bindStmt bVar (VarE accVar) -- resulting element is current accumulator
              bodyStmts_data = [bBind]

              -- BOTTOM_data (run for each element)
              -- Binding for `f`
              fVar      = var "f" uq            -- name of function to apply
              fBody     = TermE (lam2 f)        -- f's body in HOAS representation
              fBind     = bindStmt fVar fBody   -- f = <HOAS.Term>  

              fApp      = (varE fVar) `AppE` (varE accVar) `AppE` (varE aVar)
              accUpdate = assignStmt accVar fApp

              -- Increment in-segment counter
              jUpdate  = assignStmt jVar ((varE plusFn) `AppE` (varE jVar) `AppE` (LitE (1::Int)))

              botStmts_data = [fBind, accUpdate, jUpdate]

              -- LOOP
              loop      = setArrResult uq
                        $ setScalarResult accVar
                        -- Segd (segd_uq) stuff below
                        $ segd2dataJump
                        $ addStmts initStmts_segd (initLbl segd_uq)
                        $ addStmts bodyStmts_segd (bodyLbl segd_uq)
                        $ linkDones
                        -- Data (arr_uq/uq) stuff below
                        $ linkInits
                        -- $ data2segdJump -- no final in guard
                        $ replaceStmts grdStmts_data  (guardLbl uq)
                        $ addStmts bodyStmts_data (bodyLbl uq)
                        $ addStmts botStmts_data  (bottomLbl uq)
                        -- The usual stuff
                        $ rebindIndexAndLengthVars uq arr_uq
                        -- The data loop is the same rate as the current one: unite uq/arr_uq.
                        -- This is not the case with segment descriptor loop, so just append it's blocks without merging.
                        $ addDefaultSynonymLabels uq arr_uq
                        -- Note: Order of appending matters since we want to enter arr_loop not segd_loop
                        $ Loop.append arr_loop
                        $ segd_loop
          in (loop,uq)


    -- | We store scalars in AST/ASG however, we're not yet clever about computing them.
    --   For not we assume that any scalar AST could only be constructed using Scalar constructor
    getScalar :: (Typeable e, Elt e) => (ASG e Unique) -> Unique -> Term e
    getScalar var@(VarG uq) _
        = let ast = fromJust
                  $ (getASTNode env uq) `asTypeOf` (Just var)
          in  getScalar ast uq
    getScalar (ScalarG term) _ = term
    getScalar _ _ = error "getScalar: Failed scalar lookup. Make sure the scalar argument is constructed with Scalar AST constructor."

     

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
rebindIndexVar nu old = addStmt stmt (initLbl nu)
                      . addStmt stmt (guardLbl nu)
  where stmt = bindStmt (indexVar nu) (VarE $ indexVar old)


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


instance Show (AST e) where
  show (Map _ arr) = "MapAST (" P.++ (show arr) P.++ ")"
  show (Filter _ arr) = "FilterAST (" P.++ (show arr) P.++ ")"
  show (ZipWith _ arr brr) = "ZipWithAST (" P.++ (show arr) P.++ ") (" P.++ (show brr) P.++ ")"
  show (Zip arr brr) = "ZipAST (" P.++ (show arr) P.++ ") (" P.++ (show brr) P.++ ")"
  show (Fold _ _ arr) = "FoldAST (" P.++ (show arr) P.++ ")"
  show (Manifest vec) = show vec

--map :: (Elt a, Elt b) => (a -> b) -> ArrayAST a -> ArrayAST b
--map f = Map f

--filter :: (Elt a) => (a -> Bool) -> ArrayAST a -> ArrayAST a
--filter p = Filter p

--zipWith :: (Elt a, Elt b, Elt c) => (a -> b -> c) -> ArrayAST a -> ArrayAST b -> AST (V.Vector c)
--zipWith f arr brr = ZipWith f arr brr

--zip :: (Elt a, Elt b) => ArrayAST a -> ArrayAST b -> AST (V.Vector (a,b))
--zip arr brr = Zip arr brr

--fold :: Elt a => (a -> a -> a) -> a -> ArrayAST a -> a
--fold f z arr = evalAST $ Fold f z arr

--toList :: Elt a => ArrayAST a -> [a]
--toList = V.toList . eval
fromList :: Elt a => [a] -> ArrayAST a
fromList = Manifest . V.fromList


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
fl = Data.LiveFusion.Combinators.fromList


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

example1 :: ArrayAST Int
example1 = Map (+1) $ Map (*2) (fl [1,2,3])

test1 :: IO ()
test1 = print $ eval example1

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