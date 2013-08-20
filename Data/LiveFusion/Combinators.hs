{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes, FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts, NoMonomorphismRestriction, TypeOperators, NamedFieldPuns #-}
module Data.LiveFusion.Combinators where

import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.Util
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
import Data.List as List ( union )
import Data.Dynamic


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


fuse :: Typeable e => Map Unique (WrappedAST Unique) -> (AST2 e Unique) -> Unique -> (Loop, Var)
fuse env = fuse'
  where
    fuse' :: Typeable e => (AST2 e Unique) -> Unique -> (Loop, Var)
    fuse' var@(Var2 uq) _
        = let ast = fromJust
                  $ (getASTNode env uq) `asTypeOf` (Just var)
          in  fuse' ast uq
    fuse' (Map2 f arr) uq
        = let (arr_loop, aVar) = fuse' arr uq -- TODO: this uq means nothing
              bVar = var "map_x" uq
              fVar = var "map_f" uq
              loop = addArg fVar (toDyn f)
                   $ addBind bVar (App1 fVar aVar)
                   $ arr_loop
          in  (loop, bVar)
    fuse' (ZipWith2 f arr brr) uq
        = let (arr_loop, aVar) = fuse' arr uq
              (brr_loop, bVar) = fuse' brr uq
              abrr_loop = arr_loop `Loop.append` brr_loop
              cVar = var "zipWith_x" uq
              fVar = var "zipWith_f" uq
              loop = addArg fVar (toDyn f)
                   $ addBind cVar (App2 fVar aVar bVar)
                   $ abrr_loop
          in  (loop, cVar)
    fuse' (Filter2 p arr) uq
        = let (arr_loop, aVar) = fuse' arr uq
              pVar = var "filter_p" uq
              loop = addArg pVar (toDyn p)
                   $ addSkipGuard (App1 pVar aVar)
                   $ arr_loop
          in  (loop, aVar) -- Reuse result of arr
    fuse' (Scan2 f z arr) uq
        = let (arr_loop, aVar) = fuse' arr uq
              fVar = var "scan_f" uq
              zVar = var "scan_z" uq
              loop = addArg fVar (toDyn f)
                   $ addArg zVar (toDyn z)
--                   $ addBind uq (App2 fVar aVar zVar)
--                   $ addLoopArg uq acc_uq
--                   $ addPost uq (App2 (Arg
                   $ arr_loop
          in  (loop, zVar)
    fuse' (ArrLit2 vec) uq
        = let arrVar = var "arr" uq
              aVar   = var "arr_x" uq    -- result of every read
              iVar   = Var "i"           -- index is a state variable
              iInit  = App1 (Var "return") (Var "0") -- TODO: Ugly ugly ugly hack
              iUpd   = incrExpr iVar
              loop   = setLen (V.length vec)
                     $ addArg arrVar (toDyn vec)
                     $ addState iVar iInit iUpd
                     $ addBind aVar (readArrayExpr arrVar iVar)
                     $ addExitGuard (ltExpr iVar (Var "n")) -- TODO change `n' to something reasonable
                     $ Loop.empty
          in  (loop, aVar) -- TODO return a result that maps an element of array


var :: String -> Unique -> Var
var desc uq = Var $ desc ++ show uq


pluginCode :: Typeable e => AST e -> String -> String -> IO (String, [Arg])
pluginCode ast moduleName entryFnName = do
  (env, rootUq, Just rootNode) <- recoverSharing ast
  let (loop, resultVar) = fuse env rootNode rootUq
      (bodyCode, args) = pluginEntryCode entryFnName (typeOf $ resultType ast) resultVar loop
      code = preamble moduleName ++\ bodyCode
  return (code, args)


justCode :: Typeable e => AST e -> IO ()
justCode ast = putStrLn =<< indexed <$> fst <$> pluginCode ast "Plugin" "pluginEntry"

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

fold :: Elt a => (a -> a -> a) -> a -> ArrayAST a -> a
fold f z arr = evalAST $ Fold f z arr

toList :: Elt a => ArrayAST a -> [a]
toList = V.toList . eval

fromList :: Elt a => [a] -> ArrayAST a
fromList = ArrLit . V.fromList

eval :: Elt a => ArrayAST a -> V.Vector a
eval (ArrLit vec) = vec
eval op = evalAST op

evalAST :: Typeable a => AST a -> a
evalAST = unsafePerformIO . evalIO
{-# NOINLINE evalAST #-}

evalIO :: Typeable a => AST a -> IO a
evalIO ast = do
  (pluginPath, h, moduleName) <- openTempModuleFile
  let entryFnName  = "entry" ++ moduleName
  (code, args) <- pluginCode ast moduleName entryFnName
  dump code h
  pluginEntry <- compileAndLoad pluginPath moduleName entryFnName
  let result = pluginEntry args
  return $ fromJust $ fromDynamic result
{-# NOINLINE evalIO #-}

dump :: String -> Handle -> IO ()
dump code h = hPutStrLn h code >> hClose h

openTempModuleFile :: IO (FilePath, Handle, String)
openTempModuleFile = do
  (fp, h) <- openTempFile "/tmp/" "Plugin.hs" -- TODO: Make cross-platform
  let moduleName = takeBaseName fp
  return (fp, h, moduleName)

compileAndLoad :: FilePath -> String -> String -> IO ([Arg] -> Arg)
compileAndLoad hsFilePath moduleName entryFnName =
    defaultErrorHandler defaultFatalMessager defaultFlushOut $ do
      runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        setSessionDynFlags dflags
        target <- guessTarget hsFilePath Nothing
        setTargets [target]
        r <- load LoadAllTargets
        case r of
          Failed    -> error "Compilation failed"
          Succeeded -> do
            setContext [IIDecl $ simpleImportDecl (mkModuleName moduleName)]
            pluginEntry <- compileExpr (moduleName ++ "." ++ entryFnName)
            let pluginEntry' = unsafeCoerce pluginEntry :: [Arg] -> Arg
            return pluginEntry'

{-
execFnGhc :: String -> String -> HscEnv -> Ghc HValue
execFnGhc modname fn ses = do
        mod <- findModule (mkModuleName modname) Nothing
        --setContext [mod]
        --unafePerformIO $ putStrLn (moduleNameString $ moduleName mod)
        setSession ses
        compileExpr (modname ++ "." ++ fn)
-}
{-
hello :: IO HValue
hello = do
    (err, ses) <- compileAndLoadPlugin
    result <- execFnGhc "Plugin" "getInt" ses
    return result
-}
{-
loadSourceGhc :: String -> Ghc (Maybe String)
loadSourceGhc path = let
        throwingLogger (Just e) = throw e
        throwingLogger _ = return ()
    in do
        dflags <- getSessionDynFlags
        setSessionDynFlags (dflags{
            ghcLink = LinkInMemory,df            hscTarget = HscInterpreted,
            packageFlags = [ExposePackage "ghc"]
            })
        target <- guessTarget path Nothing
        addTarget target
        r <- loadWithLogger throwingLogger LoadAllTargets
        case r of
            Failed    -> return $ Just "Generic module load error"
            Succeeded -> return Nothing

        `gcatch` \(e :: SourceError) -> let
                errors e = concat $ P.map show (bagToList $ srcErrorMessages e)
            in
                return $ Just (errors e)
-}

-------------- Tests -------------------------
fl = Data.LiveFusion.Combinators.fromList

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