{-# LANGUAGE GADTs, OverloadedStrings, ScopedTypeVariables, TypeFamilies, RankNTypes, FlexibleInstances, StandaloneDeriving, DeriveDataTypeable, FlexibleContexts, NoMonomorphismRestriction, TypeOperators, NamedFieldPuns #-}
module Data.LiveFusion.Combinators where

import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.Util

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

recoverSharing :: Typeable e => AST e -> IO (Map Name (WrappedAST Name), Name, Maybe (AST2 e Name))
recoverSharing e = do
  Graph l n <- reifyGraph e
  let m = Map.fromList l
  return (m, n, getVar m n)
{-# NOINLINE recoverSharing #-}


fuse :: Typeable e => Map Name (WrappedAST Name) -> (AST2 e Name) -> Name -> (Name, Loop, Name)
fuse env = fuse'
  where
    fuse' :: Typeable e => (AST2 e Name) -> Name -> (Name, Loop, Name)
    fuse' var@(Var name) _
        = let ast = fromJust
                  $ (getVar env name) `asTypeOf` (Just var)
         in  fuse' ast name
    fuse' (Map2 f arr) name
        = let (arr_name, arr_loop, arr_res) = fuse' arr name -- TODO: this name means nothing
              loop = addArg name (toDyn f)
                   $ addBind name (App1 (ArgE name) (VarE arr_res))
                   $ arr_loop
          in  (name, loop, name)
    fuse' (ZipWith2 f arr brr) name
        = let (arr_name, arr_loop, arr_res) = fuse' arr name
              (brr_name, brr_loop, brr_res) = fuse' brr name
              abrr_loop = arr_loop `Loop.append` brr_loop
              loop = addArg name (toDyn f)
                   $ addBind name (App2 (ArgE name) (VarE arr_res) (VarE brr_res))
                   $ abrr_loop
          in  (name, loop, name)
    fuse' (Filter2 p arr) name
        = let (arr_name, arr_loop, arr_res) = fuse' arr name
              loop = addArg name (toDyn p)
                   $ addGuard (App1 (ArgE name) (VarE arr_res))
                   $ arr_loop
          in  (name, loop, name)
    fuse' (ArrLit2 vec) name
        = let loop = setLen (V.length vec)
                   $ addArg name (toDyn vec)
                   $ addVec name
                   $ Loop.empty
          in  (name, loop, name)



pluginCode :: Typeable e => AST e -> String -> String -> IO (String, [Arg])
pluginCode ast moduleName entryFnName = do
  (env, rootName, Just rootNode) <- recoverSharing ast
  let (_, loop, _) = fuse env rootNode rootName
      (bodyCode, args) = pluginEntryCode entryFnName rootNode rootName loop
      code = preamble moduleName ++\ bodyCode
  return (code, args)


justCode :: Typeable e => AST e -> IO ()
justCode ast = putStrLn =<< indexed <$> fst <$> pluginCode ast "Plugin" "pluginEntry"

pluginEntryCode :: Typeable a => String -> AST2 a Name -> Name -> Loop -> (String, [Arg])
pluginEntryCode entryFnName ast rootName loop
  = let code = entryFnName ++ " :: [Dynamic] -> Dynamic" ++\
               entryFnName `space` argsMatch ++\
               "  = toDyn $ runST $ loopST " ++ argsPass ++\
               " " ++\
               lSTCode
    in  (code, Map.elems arguments)
  where
    arguments = args loop
    lSTCode   = loopSTCode (typeOf $ resultType ast) rootName loop
    argsMatch = showStringList $ P.map arg argNames   -- "[arg1, arg2, ...]"
    argsPass  = juxtMap coerceArg argNames  -- "(fd arg1) (fd arg2) ... "
    coerceArg = paren . ("fd "++) . arg      -- "(fd arg1)"
    argNames  = Map.keys arguments
    resultType :: t a b -> a
    resultType _ = undefined


loopSTCode :: TypeRep -> Name -> Loop -> String
loopSTCode resultTy rootName (Loop args binds guards arrs len)
  = "loopST :: " ++ argsTypes ++ " -> ST s " ++ (paren $ show resultTy) ++\
    "loopST " ++ argsList ++ " =" ++\
    "  do {" ++\
    "    dst <- MV.new n" ++:\
    "    loop dst 0" ++:\
    "    dst' <- V.unsafeFreeze dst" ++:\
    "    return dst' }" ++\
    "  where {" ++\
    "    n = " ++ (show len) ++:\
    "    loop dst i = case i < n of {" ++\
    "      True  -> " ++\
    "        let { " ++\ indent 5 letsCode ++
    "        } in do {" ++\
    "          MV.unsafeWrite dst i " ++ (var rootName) ++:\
    "          loop dst (i+1)" ++\
    "        }" ++:\
    "      False -> return () }}"
  where
    (argNames, argVals) = P.unzip $ Map.toList args
    argsTypes = P.intercalate " -> "
              $ P.map (paren . show . dynTypeRep) argVals
    argsList  = P.intercalate " "
              $ P.map arg argNames
    letsCode = P.intercalate ";\n"
             $ takesCode arrs ++ bindsCode binds
    -- reads elements from the arrays



takesCode :: [Name] -> [String]
takesCode = P.map takeCode
  where
    takeCode name = (var name) ++ " = V.unsafeIndex " ++ (arg name) `space` "i" -- TODO horrible

bindsCode :: (Map Name Expr) -> [String]
bindsCode = P.map bindCode . Map.toList
  where
    bindCode (name, expr) = (lhs name) ++ " = " ++ (rhs expr)
    lhs = var
    rhs (App1 fun arg)       = (vargCode fun)  `space` (vargCode arg)
    rhs (App2 fun arg1 arg2) = (vargCode fun)  `space`
                               (vargCode arg1) `space`
                               (vargCode arg2)
    vargCode (VarE name) = var name
    vargCode (ArgE name) = arg name


pprArg :: Int -> String
pprArg ix = "arg" ++ (show ix)

pprUCArg :: Typeable a => Int -> a -> String
pprUCArg ix a = ("unsafeCoerce " ++ (pprArg ix)) `pprAsTy` a

pprAsTy :: Typeable a => String -> a -> String
pprAsTy var a = paren $ var ++ " :: " ++ (show $ typeOf a)


preamble :: String -> String
preamble moduleName =
  "module " ++ moduleName ++ " where       " ++\
  "import Data.Vector.Unboxed as V         " ++\
  "import Data.Vector.Unboxed.Mutable as MV" ++\
  "import Unsafe.Coerce                    " ++\
  "import Data.Dynamic                     " ++\
  "import GHC.Prim (Any)                   " ++\
  "import Control.Monad.ST                 " ++\
  "                                        " ++\
  "fd :: Typeable a => Dynamic -> a        " ++\
  "fd d = case fromDynamic d of            " ++\
  "         Just v  -> v                   " ++\
  "         Nothing -> error \"Argument type mismatch\"" ++\
  "                                        "

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

--main = mapM_ (print . eval) [test1, testMap1, testFilt1, testZipWith1, testMap2, testZipWith2, testZip1]

runTests = do
  let runTest = print . eval
  runTest testMap1
  runTest manymaps
  runTest testShare
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

manymaps :: ArrayAST Int
manymaps = map (+1) $ map (+2) $ map (+3) $ fl [1,2,3]

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