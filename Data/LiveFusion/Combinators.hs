{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes, FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts, NoMonomorphismRestriction, TypeOperators, NamedFieldPuns #-}
module Data.LiveFusion.Combinators where

import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.Util
import Data.LiveFusion.HsEvaluator
import Data.LiveFusion.HsCodeGen -- only for testing

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

class (Show a, V.Unbox a, Typeable a) => Elt a

instance Elt Int
instance Elt Float
instance Elt Double
instance Elt Bool
instance (Elt a, Elt b) => Elt (a,b)


type ArrayDET a = DET (V.Vector a)


-- | Delayed Evaluation Tree
data DET e where
  Map      :: (Elt a, Elt b)
           => (a -> b)
           -> ArrayDET a
           -> ArrayDET b

  Filter   :: Elt a
           => (a -> Bool)
           -> ArrayDET a
           -> ArrayDET a

  ZipWith  :: (Elt a, Elt b, Elt c)
           => (a -> b -> c)
           -> ArrayDET a
           -> ArrayDET b
           -> ArrayDET c

  Zip      :: (Elt a, Elt b)
           => ArrayDET a
           -> ArrayDET b
           -> ArrayDET (a,b)

  Fold     :: Elt a
           => (a -> a -> a)
           -> a
           -> ArrayDET a
           -> DET a

  Scan     :: Elt a
           => (a -> a -> a)
           -> a
           -> ArrayDET a
           -> ArrayDET a

  Fold_s   :: Elt a
           => (a -> a -> a)
           -> a
           -> ArrayDET Int
           -> ArrayDET a
           -> ArrayDET a

  Manifest :: Elt a
           => V.Vector a
           -> ArrayDET a

  Scalar   :: Elt a
           => a
           -> DET a


-- Required for getting data-reify to work with GADTs
data WrappedDET s where
  Wrap :: Typeable e => DEG e s -> WrappedDET s


deriving instance Show (WrappedDET Unique)


type ArrayDEG a s = DEG (V.Vector a) s


-- | Delayed Evaluation Graph
data DEG e s where
  MapG      :: (Elt a, Elt b)
            => (a -> b)
            -> ArrayDEG a s
            -> ArrayDEG b s

  FilterG   :: Elt a
            => (a -> Bool)
            -> ArrayDEG a s
            -> ArrayDEG a s

  ZipWithG  :: (Elt a, Elt b, Elt c)
            => (a -> b -> c)
            -> ArrayDEG a s
            -> ArrayDEG b s
            -> ArrayDEG c s

  ZipG      :: (Elt a, Elt b)
            => ArrayDEG a s
            -> ArrayDEG b s
            -> ArrayDEG (a,b) s

  FoldG     :: Elt a
            => (a -> a -> a)
            -> a
            -> ArrayDEG a s
            -> DEG a s

  ScanG     :: Elt a => (a -> a -> a)
            -> a
            -> ArrayDEG a s
            -> ArrayDEG a s

  ManifestG :: Elt a
            => V.Vector a
            -> ArrayDEG a s

  ScalarG   :: Elt a
            => a
            -> DEG a s

  Fold_sG   :: Elt a
            => (a -> a -> a)
            -> a
            -> ArrayDEG Int s
            -> ArrayDEG a s
            -> ArrayDEG a s

  VarG      :: Typeable e
            => s
            -> DEG e s


deriving instance Show s => Show (DEG e s)
deriving instance Typeable2 DEG

instance Typeable e => MuRef (DET e) where
  type DeRef (DET e) = WrappedDET
  mapDeRef ap e = Wrap <$> mapDeRef' ap e
    where
      mapDeRef' :: Applicative ap
                => (forall b. (MuRef b, WrappedDET ~ DeRef b) => b -> ap u)
                -> DET e
                -> ap (DEG e u)

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
        = FoldG f z
          <$> (VarG <$> ap arr)

      mapDeRef' ap (Scan f z arr)
        = ScanG f z
          <$> (VarG <$> ap arr)

      mapDeRef' ap (Fold_s f z lens arr)
        = Fold_sG f z
          <$> (VarG <$> ap lens)
          <*> (VarG <$> ap arr)

      mapDeRef' ap (Manifest vec)
        = pure $ ManifestG vec

      mapDeRef' ap (Scalar x)
        = pure $ ScalarG x

-- This is confusing at the moment: Var refers Unique that identifies the tree node we want to fetch
getDETNode :: Typeable e => Map Unique (WrappedDET Unique) -> Unique -> Maybe (DEG e Unique)
getDETNode m n = case m ! n of Wrap  e -> cast e

recoverSharing :: Typeable e => DET e -> IO (Map Unique (WrappedDET Unique), Unique, Maybe (DEG e Unique))
recoverSharing e = do
  Graph l n <- reifyGraph e
  let m = Map.fromList l
  return (m, n, getDETNode m n)
{-# NOINLINE recoverSharing #-}


fuse :: Typeable e => Map Unique (WrappedDET Unique) -> (DEG e Unique) -> Unique -> (Loop, Unique)
fuse env = fuse'
  where
    fuse' :: Typeable e => (DEG e Unique) -> Unique -> (Loop, Unique)
    -- TODO: Unique id argument is essentially threaded through, can we abstract?
    fuse' var@(VarG uq) _
        = let det = fromJust
                  $ (getDETNode env uq) `asTypeOf` (Just var)
          in  fuse' det uq

    fuse' (ManifestG vec) uq
        = let arrVar    = arrayVar uq

              -- BODY
              aVar      = eltVar uq                   -- result of every read
              aBind     = bindStmt aVar (App2 readFn ixVar arrVar) -- read statement
              bodyStmts = [aBind]

              -- INIT
              lenVar    = lengthVar uq
              lenBind   = bindStmt lenVar (App1 lengthFn arrVar)
              ixVar     = indexVar uq                 -- index
              ixInit    = bindStmt ixVar (IntLit 0)   -- index initialization
              initStmts = [ixInit, lenBind]

              -- BOTTOM
              oneVar    = var "one" uq
              oneBind   = bindStmt oneVar (IntLit 1)  -- index step
              ixUpdate  = assignStmt ixVar (App2 plusFn ixVar oneVar)
              botStmts  = [oneBind, ixUpdate]

              -- GUARD
              predVar   = var "pred" uq -- boolean guard predicate
              predBind  = bindStmt predVar (App2 ltFn ixVar lenVar)
              ixGuard   = guardStmt predVar (doneLbl uq)
              grdStmts  = [predBind, ixGuard]

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
              fVar      = var "f" uq            -- name of function to apply
              fApp      = App1 fVar aVar        -- function application
              bVar      = eltVar uq             -- resulting element variable
              bBind     = bindStmt bVar fApp    -- bind result
              bodyStmts = [bBind]               -- body block is just assignment

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg fVar (toDyn f)
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
              cVar      = eltVar uq
              fVar      = var "f" uq
              fApp      = App2 fVar aVar bVar
              cBind     = bindStmt cVar fApp
              bodyStmts = [cBind]

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg fVar (toDyn f)
                        $ addStmts bodyStmts (bodyLbl uq)
                        $ rebindIndexAndLengthVars uq arr_uq -- be careful: arbitrary choice between a and b
                        -- $ addDefaultControlFlow uq
                        $ abrr_loop
          in  (loop, uq)

    fuse' (FilterG p arr) uq
        = let (arr_loop, arr_uq) = fuse' arr uq
              aVar      = eltVar arr_uq

              -- INIT
              ixVar     = indexVar uq                 -- writing index
              ixInit    = bindStmt ixVar (IntLit 0)    -- index initialization
              initStmts = [ixInit]

              -- BODY
              pVar      = var "p" uq
              pApp      = App1 pVar aVar
              boolVar   = var "bool" uq
              boolBind  = bindStmt boolVar pApp
              guard     = guardStmt boolVar (bottomLbl uq)
              resVar    = eltVar uq
              resBind   = bindStmt resVar (VarE aVar)
              -- NOTE: This will bug out if there are more guards
              --       or anything else important in the remainder of the body
              bodyStmts = [boolBind, guard, resBind]

              -- WRITE
              -- WARNING: Assignment statement preceeds the array write stmt (added in the postprocess step)
              --          It it fine with the current semantics as the unupdated index will be used,
              --          however this is error prone and may not be true with code gens other than HsCodeGen.
              oneVar    = var "one" uq
              oneBind   = bindStmt oneVar (IntLit 1)  -- index step
              ixUpdate  = assignStmt ixVar (App2 plusFn ixVar oneVar)
              writeStmts = [oneBind, ixUpdate]

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg pVar (toDyn p)
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
              fVar      = var "f" uq
              zVar      = var "z" uq
              -- INIT
              accVar    = var "acc" uq                -- accumulator
              accInit   = bindStmt accVar (VarE zVar)  -- accum initialization
              initStmts = [accInit]
              -- BODY
              bVar      = eltVar uq
              bBind     = bindStmt bVar (VarE accVar) -- resulting element in current accum
              bodyStmts = [bBind]
              -- BOTTOM
              fApp      = App2 fVar accVar aVar
              accUpdate = assignStmt accVar fApp
              botStmts  = [accUpdate]
              -- LOOP
              loop      = setArrResult uq
                        $ setScalarResult accVar
                        $ addArg fVar (toDyn f)
                        $ addArg zVar (toDyn z)
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
     

-- | Sets the upper bound of an array to be the same as that
--   of another array.
rebindLengthVar :: Unique -> Unique -> Loop -> Loop
rebindLengthVar nu old = addStmt stmt (initLbl nu)
  where stmt = bindStmt (lengthVar nu) (VarE $ lengthVar old)


rebindIndexVar :: Unique -> Unique -> Loop -> Loop
rebindIndexVar nu old = addStmt stmt (initLbl nu)
  where stmt = bindStmt (indexVar nu) (VarE $ indexVar old)


rebindIndexAndLengthVars :: Unique -> Unique -> Loop -> Loop
rebindIndexAndLengthVars nu old = rebindLengthVar nu old
                                . rebindIndexVar nu old


{-
puginCode :: Typeable e => DET e -> String -> String -> IO (String, [Arg])
pluginCode DET moduleName entryFnName = do
  (env, rootUq, Just rootNode) <- recoverSharing DET
  let (loop, resultVar) = fuse env rootNode rootUq
      (bodyCode, args) = pluginEntryCode entryFnName (typeOf $ resultType DET) resultVar loop
      code = preamble moduleName ++\ bodyCode
  return (code, args)


justCode :: Typeable e => DET e -> IO ()
justCode DET = putStrLn =<< indexed <$> fst <$> pluginCode DET "Plugin" "pluginEntry"
-}
fuseToLoop :: Typeable e => DET e -> IO Loop
fuseToLoop det = do
  (env, rootUq, Just rootNode) <- recoverSharing det
  let (loop, resultUq) = fuse env rootNode rootUq
  return loop


resultType :: t a -> a
resultType _ = undefined


instance Show (DET e) where
  show (Map _ arr) = "MapDET (" P.++ (show arr) P.++ ")"
  show (Filter _ arr) = "FilterDET (" P.++ (show arr) P.++ ")"
  show (ZipWith _ arr brr) = "ZipWithDET (" P.++ (show arr) P.++ ") (" P.++ (show brr) P.++ ")"
  show (Zip arr brr) = "ZipDET (" P.++ (show arr) P.++ ") (" P.++ (show brr) P.++ ")"
  show (Fold _ _ arr) = "FoldDET (" P.++ (show arr) P.++ ")"
  show (Manifest vec) = show vec

--map :: (Elt a, Elt b) => (a -> b) -> ArrayDET a -> ArrayDET b
--map f = Map f

--filter :: (Elt a) => (a -> Bool) -> ArrayDET a -> ArrayDET a
--filter p = Filter p

--zipWith :: (Elt a, Elt b, Elt c) => (a -> b -> c) -> ArrayDET a -> ArrayDET b -> DET (V.Vector c)
--zipWith f arr brr = ZipWith f arr brr

--zip :: (Elt a, Elt b) => ArrayDET a -> ArrayDET b -> DET (V.Vector (a,b))
--zip arr brr = Zip arr brr

--fold :: Elt a => (a -> a -> a) -> a -> ArrayDET a -> a
--fold f z arr = evalDET $ Fold f z arr

--toList :: Elt a => ArrayDET a -> [a]
--toList = V.toList . eval
fromList :: Elt a => [a] -> ArrayDET a
fromList = Manifest . V.fromList


eval :: Elt a => ArrayDET a -> V.Vector a
eval (Manifest vec) = vec
eval op = evalDET op

evalDET :: Typeable a => DET a -> a
evalDET det = result
  where
    loop = getLoop det
    dynResult = evalLoop loop
    result = fromJust $ fromDynamic dynResult
{-# NOINLINE evalDET #-}

getLoop :: Typeable a => DET a -> Loop
getLoop = postprocessLoop . unsafePerformIO . fuseToLoop
{-# NOINLINE getLoop #-}

-------------- Tests -------------------------
fl = Data.LiveFusion.Combinators.fromList


example0 :: ArrayDET Int
example0 = ZipWith (+)
        (fl [1,2,3])
      $ Scan (+) 0 $ Filter (const True) $ Map (+1) $ fl [4,5,6]


test0 :: IO ()
test0 = print $ eval example0

{-
runTests = do
  let runTest = print . eval
  mapM_ runTest [ test1, testMap1, testFilt1, testZipWith1, testMapG
                , testZipWithG, {- testZip1, -} testShare, testManyMaps]
  runTest testMZW

test1 :: ArrayDET Int
test1 = zipWith (*) (map (+1) $ fl [1,2,3,4,5,6,7,8]) (zipWith (+) (filter (<0) $ fl $ take 20 [-8,-7..]) (map (\x->x*2+1) $ fl [1..8]))

testMap1 :: ArrayDET Int
testMap1 = map (\x->x*2+1) $ fl [1..8]

testFilt1 :: ArrayDET Int
testFilt1 = filter (<0) $ fl $ take 20 [-8,-7..]

testZipWith1 :: ArrayDET Int
testZipWith1 = zipWith (+) testMap1 testFilt1

testMapG :: ArrayDET Int
testMapG = map (+1) $ fl [1,2,3,4,5,6,7,8]

testZipWithG :: ArrayDET Int
testZipWithG = zipWith (*) testMapG testZipWith1

testZip1 :: ArrayDET Int
testZip1 = map (uncurry (*)) $ zip testMapG testZipWith1

testShare :: ArrayDET Int
testShare = zipWith (+) (map (+1) arr) (map (+2) arr)
  where arr = fl [1,2,3]

testManyMaps :: ArrayDET Int
testManyMaps = map (+1) $ map (+2) $ map (+3) $ fl [1,2,3]

testMZW :: ArrayDET (Int,Double)
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