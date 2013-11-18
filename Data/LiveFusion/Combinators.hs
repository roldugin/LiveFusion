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

type ArrayAST a = AST (V.Vector a)

data AST e where
  Map     :: (Elt a, Elt b) => (a -> b) -> ArrayAST a -> ArrayAST b
  Filter  :: Elt a => (a -> Bool) -> ArrayAST a -> ArrayAST a
  ZipWith :: (Elt a, Elt b, Elt c) => (a -> b -> c) -> ArrayAST a -> ArrayAST b -> ArrayAST c
  Zip     :: (Elt a, Elt b) => ArrayAST a -> ArrayAST b -> ArrayAST (a,b)
  Fold    :: Elt a => (a -> a -> a) -> a -> ArrayAST a -> AST a
  Scan    :: Elt a => (a -> a -> a) -> a -> ArrayAST a -> ArrayAST a
  ArrLit  :: Elt a => V.Vector a -> ArrayAST a

-- Required for getting data-reify to work with GADTs
data WrappedAST s where
  Wrap :: Typeable e => AST2 e s -> WrappedAST s

deriving instance Show (WrappedAST Unique)

type ArrayAST2 a s = AST2 (V.Vector a) s

data AST2 e s where
  Map2     :: (Elt a, Elt b) => (a -> b) -> ArrayAST2 a s -> ArrayAST2 b s
  Filter2  :: Elt a => (a -> Bool) -> ArrayAST2 a s -> ArrayAST2 a s
  ZipWith2 :: (Elt a, Elt b, Elt c) => (a -> b -> c) -> ArrayAST2 a s -> ArrayAST2 b s -> ArrayAST2 c s
  Zip2     :: (Elt a, Elt b) => ArrayAST2 a s -> ArrayAST2 b s -> ArrayAST2 (a,b) s
  Fold2    :: Elt a => (a -> a -> a) -> a -> ArrayAST2 a s -> AST2 a s
  Scan2    :: Elt a => (a -> a -> a) -> a -> ArrayAST2 a s -> ArrayAST2 a s
  ArrLit2  :: Elt a => V.Vector a -> ArrayAST2 a s
  Var2     :: Typeable e => s -> AST2 e s


deriving instance Show s => Show (AST2 e s)
deriving instance Typeable2 AST2

instance Typeable e => MuRef (AST e) where
  type DeRef (AST e) = WrappedAST
  mapDeRef ap e = Wrap <$> mapDeRef' ap e
    where
      mapDeRef' :: Applicative ap
                => (forall b. (MuRef b, WrappedAST ~ DeRef b) => b -> ap u)
                -> AST e
                -> ap (AST2 e u)
      mapDeRef' ap (Map f arr)    = Map2 f <$> (Var2 <$> ap arr)
      mapDeRef' ap (Filter p arr) = Filter2 p <$> (Var2 <$> ap arr)
      mapDeRef' ap (ZipWith f arr brr) = ZipWith2 f <$> (Var2 <$> ap arr) <*> (Var2 <$> ap brr)
      mapDeRef' ap (Zip arr brr)  = Zip2 <$> (Var2 <$> ap arr) <*> (Var2 <$> ap brr)
      mapDeRef' ap (Fold f z arr) = Fold2 f z <$> (Var2 <$> ap arr)
      mapDeRef' ap (Scan f z arr) = Scan2 f z <$> (Var2 <$> ap arr)
      mapDeRef' ap (ArrLit vec)   = pure $ ArrLit2 vec

-- This is confusing as the moment: Var refers Unique that identifies the tree node we want to fetch
getASTNode :: Typeable e => Map Unique (WrappedAST Unique) -> Unique -> Maybe (AST2 e Unique)
getASTNode m n = case m ! n of Wrap  e -> cast e

recoverSharing :: Typeable e => AST e -> IO (Map Unique (WrappedAST Unique), Unique, Maybe (AST2 e Unique))
recoverSharing e = do
  Graph l n <- reifyGraph e
  let m = Map.fromList l
  return (m, n, getASTNode m n)
{-# NOINLINE recoverSharing #-}


fuse :: Typeable e => Map Unique (WrappedAST Unique) -> (AST2 e Unique) -> Unique -> (Loop, Unique)
fuse env = fuse'
  where
    fuse' :: Typeable e => (AST2 e Unique) -> Unique -> (Loop, Unique)
    -- TODO: Unique id argument is essentially threaded through, can we abstract?
    fuse' var@(Var2 uq) _
        = let ast = fromJust
                  $ (getASTNode env uq) `asTypeOf` (Just var)
          in  fuse' ast uq

    fuse' (ArrLit2 vec) uq
        = let arrVar    = arrayVar uq

              -- BODY
              aVar      = eltVar uq                   -- result of every read
              aBind     = bindStmt aVar (App2 readFn ixVar arrVar) -- read statement
              bodyStmts = [aBind]

              -- INIT
              lenVar    = lengthVar uq
              lenBind   = bindStmt lenVar (App1 lengthFn arrVar)
              ixVar     = indexVar uq                 -- index
              ixInit    = bindStmt ixVar (IntLit 0)    -- index initialization
              initStmts = [ixInit, lenBind]

              -- BOTTOM
              oneVar    = var "one" uq
              oneBind   = bindStmt oneVar (IntLit 1)  -- index step
              ixUpdate  = assignStmt ixVar (App2 plusFn ixVar oneVar)
              botStmts  = [oneBind, ixUpdate]

              -- GUARD
              predVar   = var "pred" uq -- boolean guard predicate
              predBind  = bindStmt predVar (App2 ltFn ixVar lenVar)
              ixGuard   = guardStmt predVar doneLbl
              grdStmts  = [predBind, ixGuard]

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg arrVar (toDyn vec)
                        $ addStmts initStmts  initLbl
                        $ addStmts grdStmts   guardLbl
                        $ addStmts bodyStmts  bodyLbl
                        $ addStmts botStmts   bottomLbl
                        $ Loop.empty
          in  (loop, uq) -- TODO return a result that maps an element of array

    fuse' (Map2 f arr) uq
        = let (arr_loop, arr_uq) = fuse' arr uq -- TODO: this uq means nothing
              aVar      = eltVar arr_uq         -- element of source array

              -- BODY
              fVar      = var "f" uq            -- name of function to apply
              fApp      = App1 fVar aVar        -- function application
              bVar      = eltVar uq             -- resulting element variable
              bBind     = bindStmt bVar fApp    -- bind result
              bodyStmts = [bBind] -- body block is just assignment

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg fVar (toDyn f)
                        $ addStmts bodyStmts bodyLbl
                        $ rebindIndexAndLengthVars uq arr_uq
                        $ arr_loop
          in  (loop, uq)

    fuse' (ZipWith2 f arr brr) uq
        = let (arr_loop, arr_uq) = fuse' arr uq
              (brr_loop, brr_uq) = fuse' brr uq
              aVar      = eltVar arr_uq
              bVar      = eltVar brr_uq
              abrr_loop = arr_loop `Loop.append` brr_loop

              -- BODY
              cVar      = eltVar uq
              fVar      = var "f" uq
              fApp      = App2 fVar aVar bVar
              cBind     = bindStmt cVar fApp
              bodyStmts = [cBind]

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg fVar (toDyn f)
                        $ addStmts bodyStmts bodyLbl
                        $ rebindIndexAndLengthVars uq arr_uq -- be careful: arbitrary choice between a and b
                        $ abrr_loop
          in  (loop, uq)

    fuse' (Filter2 p arr) uq
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
              guard     = guardStmt boolVar bottomLbl
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
              writeStmts  = [oneBind, ixUpdate]

              -- LOOP
              loop      = setArrResultOnly uq
                        $ addArg pVar (toDyn p)
                        $ addStmts initStmts initLbl
                        $ addStmts bodyStmts bodyLbl
                        $ addStmts writeStmts writeLbl
                        -- Note that we aren't rebinding index since read/write indexes are not the same with Filter
                        $ rebindLengthVar uq arr_uq
                        $ arr_loop
          in  (loop, uq)

    fuse' (Scan2 f z arr) uq
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
                        $ addStmts initStmts initLbl
                        $ addStmts bodyStmts bodyLbl
                        $ addStmts botStmts  bottomLbl
                        $ rebindIndexAndLengthVars uq arr_uq
                        $ arr_loop
          in  (loop, uq)


-- | Sets the upper bound of an array to be the same as that
--   of another array.
rebindLengthVar :: Unique -> Unique -> Loop -> Loop
rebindLengthVar nu old = addStmt stmt initLbl
  where stmt = bindStmt (lengthVar nu) (VarE $ lengthVar old)


rebindIndexVar :: Unique -> Unique -> Loop -> Loop
rebindIndexVar nu old = addStmt stmt initLbl
  where stmt = bindStmt (indexVar nu) (VarE $ indexVar old)


rebindIndexAndLengthVars :: Unique -> Unique -> Loop -> Loop
rebindIndexAndLengthVars nu old = rebindLengthVar nu old
                                . rebindIndexVar nu old


{-
pluginCode :: Typeable e => AST e -> String -> String -> IO (String, [Arg])
pluginCode ast moduleName entryFnName = do
  (env, rootUq, Just rootNode) <- recoverSharing ast
  let (loop, resultVar) = fuse env rootNode rootUq
      (bodyCode, args) = pluginEntryCode entryFnName (typeOf $ resultType ast) resultVar loop
      code = preamble moduleName ++\ bodyCode
  return (code, args)


justCode :: Typeable e => AST e -> IO ()
justCode ast = putStrLn =<< indexed <$> fst <$> pluginCode ast "Plugin" "pluginEntry"
-}

fuseToLoop :: Typeable e => AST e -> IO Loop
fuseToLoop ast = do
  (env, rootUq, Just rootNode) <- recoverSharing ast
  let (loop, resultUq) = fuse env rootNode rootUq
  return loop


resultType :: t a -> a
resultType _ = undefined


pprAsTy :: Typeable a => String -> a -> String
pprAsTy var a = paren $ var ++ " :: " ++ (show $ typeOf a)

instance Show (AST e) where
  show (Map _ arr) = "MapAST (" P.++ (show arr) P.++ ")"
  show (Filter _ arr) = "FilterAST (" P.++ (show arr) P.++ ")"
  show (ZipWith _ arr brr) = "ZipWithAST (" P.++ (show arr) P.++ ") (" P.++ (show brr) P.++ ")"
  show (Zip arr brr) = "ZipAST (" P.++ (show arr) P.++ ") (" P.++ (show brr) P.++ ")"
  show (Fold _ _ arr) = "FoldAST (" P.++ (show arr) P.++ ")"
  show (ArrLit vec) = show vec

map :: (Elt a, Elt b) => (a -> b) -> ArrayAST a -> ArrayAST b
map f = Map f

filter :: (Elt a) => (a -> Bool) -> ArrayAST a -> ArrayAST a
filter p = Filter p

zipWith :: (Elt a, Elt b, Elt c) => (a -> b -> c) -> ArrayAST a -> ArrayAST b -> AST (V.Vector c)
zipWith f arr brr = ZipWith f arr brr

zip :: (Elt a, Elt b) => ArrayAST a -> ArrayAST b -> AST (V.Vector (a,b))
zip arr brr = Zip arr brr

--fold :: Elt a => (a -> a -> a) -> a -> ArrayAST a -> a
--fold f z arr = evalAST $ Fold f z arr

--toList :: Elt a => ArrayAST a -> [a]
--toList = V.toList . eval

fromList :: Elt a => [a] -> ArrayAST a
fromList = ArrLit . V.fromList


eval :: Elt a => ArrayAST a -> V.Vector a
eval (ArrLit vec) = vec
eval op = evalAST op

evalAST :: Typeable a => AST a -> a
evalAST ast = result
  where
    loop = getLoop ast
    dynResult = evalLoop loop
    result = fromJust $ fromDynamic dynResult
{-# NOINLINE evalAST #-}

getLoop :: Typeable a => AST a -> Loop
getLoop = postprocessLoop . unsafePerformIO . fuseToLoop
{-# NOINLINE getLoop #-}

-------------- Tests -------------------------
fl = Data.LiveFusion.Combinators.fromList


example0 :: ArrayAST Int
example0 = ZipWith (+)
        (fl [1,2,3])
      $ Scan (+) 0 $ Filter (const True) $ Map (+1) $ fl [4,5,6]


test0 :: IO ()
test0 = print $ eval example0

{-
runTests = do
  let runTest = print . eval
  mapM_ runTest [ test1, testMap1, testFilt1, testZipWith1, testMap2
                , testZipWith2, {- testZip1, -} testShare, testManyMaps]
  runTest testMZW

test1 :: ArrayAST Int
test1 = zipWith (*) (map (+1) $ fl [1,2,3,4,5,6,7,8]) (zipWith (+) (filter (<0) $ fl $ take 20 [-8,-7..]) (map (\x->x*2+1) $ fl [1..8]))

testMap1 :: ArrayAST Int
testMap1 = map (\x->x*2+1) $ fl [1..8]

testFilt1 :: ArrayAST Int
testFilt1 = filter (<0) $ fl $ take 20 [-8,-7..]

testZipWith1 :: ArrayAST Int
testZipWith1 = zipWith (+) testMap1 testFilt1

testMap2 :: ArrayAST Int
testMap2 = map (+1) $ fl [1,2,3,4,5,6,7,8]

testZipWith2 :: ArrayAST Int
testZipWith2 = zipWith (*) testMap2 testZipWith1

testZip1 :: ArrayAST Int
testZip1 = map (uncurry (*)) $ zip testMap2 testZipWith1

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