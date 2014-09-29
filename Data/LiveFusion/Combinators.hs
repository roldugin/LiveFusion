{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes,
             FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts,
             NoMonomorphismRestriction, TypeOperators, NamedFieldPuns, LambdaCase, ExplicitForAll #-}
module Data.LiveFusion.Combinators where

import Data.LiveFusion.AST
import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.LoopFunctions as Loop
import Data.LiveFusion.Util
import Data.LiveFusion.HsEvaluator
import Data.LiveFusion.Types hiding ( Unique )
import Data.LiveFusion.Scalar.HOAS as HOAS
import Data.LiveFusion.Fuse
import Data.LiveFusion.Sharing

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
import Data.Maybe
import Data.List as List
import Data.Dynamic
import Control.Arrow ( (>>>) )
import Language.Haskell.TH ( pprint )


tr a = trace (show a) a

uc = unsafeCoerce

ucText = "unsafeCoerce"


fuseToLoop :: Typeable e => AST e -> IO Loop
fuseToLoop ast = do
  (env, rootUq, Just rootNode) <- recoverSharing ast
  let loop = fuse env rootNode rootUq
  return loop


resultType :: t a -> a
resultType _ = undefined


instance (Typeable e, Show e) => Show (AST e) where
  show = show . evalAST


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
