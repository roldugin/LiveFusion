{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes, FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts #-}
module Data.LiveFusion.Combinators where

import qualified Data.Vector.Unboxed as V
import Prelude hiding ( map, zip, filter, zipWith )
import qualified Prelude as P
import Unsafe.Coerce
import GHC.Prim (Any)
import qualified Data.List as P
import Data.Typeable
import GHC hiding ( Name )
import GHC.Paths -- ( libdir )
import DynFlags -- ( defaultFatalMessager, defaultFlushOut )
import Debug.Trace
import System.IO
import System.IO.Unsafe
import System.FilePath
import Data.Reify
import Data.Map as Map (Map(..), (!), fromList)
import Control.Applicative
import Text.Show.Functions

tr a = trace (show a) a

uc = unsafeCoerce

ucText = "unsafeCoerce"

type Arg = Any

class (Show a, V.Unbox a, Typeable a) => Elt a

instance Elt Int
instance Elt Float
instance Elt Double
instance (Elt a, Elt b) => Elt (a,b)

type ArrayAST a = AST (V.Vector a)

type Name = Unique

data AST e where
  Map     :: (Elt a, Elt b) => (a -> b) -> ArrayAST a -> ArrayAST b
  Filter  :: Elt a => (a -> Bool) -> ArrayAST a -> ArrayAST a
  ZipWith :: (Elt a, Elt b, Elt c) => (a -> b -> c) -> ArrayAST a -> ArrayAST b -> ArrayAST c
  Zip     :: (Elt a, Elt b) => ArrayAST a -> ArrayAST b -> ArrayAST (a,b)
  Fold    :: Elt a => (a -> a -> a) -> a -> ArrayAST a -> AST a
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
  ArrLit2  :: Elt a => V.Vector a -> ArrayAST2 a s
  Var      :: Typeable e => s -> AST2 e s

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
      mapDeRef' ap (Map f arr) = Map2 f <$> (Var <$> ap arr)
      mapDeRef' ap (Filter p arr) = Filter2 p <$> (Var <$> ap arr)
      mapDeRef' ap (ZipWith f arr brr) = ZipWith2 f <$> (Var <$> ap arr) <*> (Var <$> ap brr)
      mapDeRef' ap (Zip arr brr) = Zip2 <$> (Var <$> ap arr) <*> (Var <$> ap brr)
      mapDeRef' ap (Fold f z arr) = Fold2 f z <$> (Var <$> ap arr)
      mapDeRef' ap (ArrLit vec) = pure $ ArrLit2 vec

getVar :: Typeable e => Map Name (WrappedAST Name) -> Name -> Maybe (AST2 e Name)
getVar m n = case m ! n of Wrap  e -> cast e

conv :: Typeable e => AST e -> IO (Map Name (WrappedAST Name), Maybe (AST2 e Name))
conv e = do
  Graph l n <- reifyGraph e
  let m = Map.fromList l
  return (m, getVar m n)
{-# NOINLINE conv #-}

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

evalAST :: AST a -> a
evalAST = unsafePerformIO . evalIO
{-# NOINLINE evalAST #-}

--interpAST (Map f arr) = V.map f (eval arr)
--interpAST (Filter p arr) = V.filter p (eval arr)
--interpAST (ZipWith f arr brr) = V.zipWith f (eval arr) (eval brr)
--interpAST (Zip arr brr) = V.zip (eval arr) (eval brr)
--interpAST (Fold f z arr) = V.foldl f z (eval arr)

pluginCode :: AST a -> String -> String -> (String, [Arg])
pluginCode op moduleName entryFnName
  = let (code, args) = opCode op 0
        nargs = P.length args
        argsPat = P.intercalate ", "
                $ P.map ("arg" ++)
                $ P.map show
                $ P.reverse [0..nargs-1]
        resultCode = preamble moduleName               ++\
                     entryFnName ++ " :: [Any] -> Any" ++\
                     entryFnName ++ "[" ++ argsPat ++ "] = "
                                 ++ "unsafeCoerce " ++ paren code ++ " :: Any"
    in  (resultCode, args)

--arrayCode :: Elt a => ArrayAST a -> Int -> (String, [Arg])
--arrayCode (Manifest vec) ix = (pprUCArg ix vec, [uc vec])
--arrayCode (Delayed  op)  ix = opCode op ix

opCode :: AST a -> Int -> (String, [Arg])
opCode (Map f arr) ix
  = let (arrCode, arrArgs) = opCode arr ix
        args = (uc f) : arrArgs
        fix  = ix + P.length arrArgs
        code = "V.map " ++ (pprUCArg fix f) ++ (paren arrCode)
    in  (code, args)
opCode (Filter p arr) ix
  = let (arrCode, arrArgs) = opCode arr ix
        args = (uc p) : arrArgs
        pix  = ix + P.length arrArgs
        code = "V.filter " ++ (pprUCArg pix p) ++ (paren arrCode)
    in  (code, args)
opCode (ZipWith f arr brr) ix
  = let (brrCode, brrArgs) = opCode brr ix
        (arrCode, arrArgs) = opCode arr (P.length brrArgs)
        args = (uc f) : arrArgs ++ brrArgs
        fix  = ix + P.length arrArgs + P.length brrArgs
        code = "V.zipWith " ++ (pprUCArg fix f) ++ (paren arrCode) ++ (paren brrCode)
    in  (code, args)
opCode (Zip arr brr) ix
  = let (brrCode, brrArgs) = opCode brr ix
        (arrCode, arrArgs) = opCode arr (P.length brrArgs)
        args = arrArgs ++ brrArgs
        code = "V.zip " ++ (paren arrCode) ++ (paren brrCode)
    in  (code, args)
opCode (Fold f z arr) ix
  = let (arrCode, arrArgs) = opCode arr ix
        args = (uc f) : (uc z) : arrArgs
        zix  = ix + P.length arrArgs
        fix  = ix + P.length arrArgs + 1
        code = "V.foldl " ++ (pprUCArg fix f) ++ (pprUCArg zix z) ++ (paren arrCode)
    in  (code, args)
opCode (ArrLit vec) ix
  = (pprUCArg ix vec, [uc vec])

paren :: String -> String
paren s = "(" ++ s ++ ")"

pprArg :: Int -> String
pprArg ix = "arg" ++ (show ix)

pprUCArg :: Typeable a => Int -> a -> String
pprUCArg ix a = ("unsafeCoerce " ++ (pprArg ix)) `pprAsTy` a

pprAsTy :: Typeable a => String -> a -> String
pprAsTy var a = paren $ var ++ " :: " ++ (show $ typeOf a)

infixr 5  ++\
(++\) :: String -> String -> String
(++\) l r = l ++ "\n" ++ r

preamble :: String -> String
preamble moduleName =
  "module " ++ moduleName ++ " where" ++\
  "import Data.Vector.Unboxed as V  " ++\
  "import Unsafe.Coerce             " ++\
  "import GHC.Prim (Any)            "

evalIO :: AST a -> IO a
evalIO op = do
  (pluginPath, h, moduleName) <- openTempModuleFile
  let entryFnName  = "entry" ++ moduleName
      (code, args) = pluginCode op moduleName entryFnName
  dump code h
  pluginEntry <- compileAndLoad pluginPath moduleName entryFnName
  let result = pluginEntry args
  return $ uc result
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

runTests = mapM_ (print . eval) [test1, testMap1, testFilt1, testZipWith1, testMap2, testZipWith2, testZip1]

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
