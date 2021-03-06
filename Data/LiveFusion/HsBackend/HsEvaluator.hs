module Data.LiveFusion.HsBackend.HsEvaluator where

import Data.LiveFusion.Loop
import Data.LiveFusion.HsBackend.HsCodeGen

import qualified Data.Vector.Unboxed as V
import Prelude hiding ( map, zip, filter, zipWith )
import qualified Prelude as P
import Unsafe.Coerce
import GHC.Prim (Any)
import qualified Data.List as P
import Data.Typeable
import GHC hiding ( Unique, pprExpr )
import GHC.Paths -- ( libdir )
import DynFlags -- ( defaultFatalMessager, defaultFlushOut )
import Control.Exception
import Control.Monad
import Debug.Trace
import System.IO
import System.IO.Unsafe
import System.FilePath
import Data.Reify
import Data.Reify.Graph
import Data.Dynamic
import Data.Map as Map ( elems )
import Data.Functor


-- | Set this to enable/disable dumping GHC core of compiled plugins
--
-- NOTE: This won't work from inside GHCi.
dEBUG_DUMP :: Bool
dEBUG_DUMP = False


defaultEntryFunctionName :: String
defaultEntryFunctionName = "entry_"

-- | The loop language is currently untyped so TypeRep argument is the type of the result.
evalLoop :: Loop -> TypeRep -> Dynamic
evalLoop loop = unsafePerformIO . evalLoopIO loop
{-# NOINLINE evalLoop #-}

-- | The loop language is currently untyped so TypeRep argumer is the type of the result.
evalLoopIO :: Loop -> TypeRep -> IO Dynamic
evalLoopIO loop resultTy = do
  (pluginPath, h, moduleName) <- openTempModuleFile
  let entryFnName  = defaultEntryFunctionName ++ moduleName
  let codeString   = pluginCode moduleName entryFnName loop resultTy
  dump codeString h
  pluginEntry <- compileAndLoad pluginPath moduleName entryFnName
  let args    = Map.elems $ loopArgs loop
  let result  = pluginEntry args
  return result

openTempModuleFile :: IO (FilePath, Handle, String)
openTempModuleFile = do
  (fp, h) <- openTempFile "/tmp/" "Plugin.hs" -- TODO: Make cross-platform
  let moduleName = takeBaseName fp
  return (fp, h, moduleName)

dump :: String -> Handle -> IO ()
dump code h = hPutStrLn h code >> hClose h

compileAndLoad :: FilePath -> String -> String -> IO ([Arg] -> Arg)
compileAndLoad hsFilePath moduleName entryFnName =
    defaultErrorHandler defaultFatalMessager defaultFlushOut $ do
      when dEBUG_DUMP
        (void $ parseStaticFlags $ noLoc <$> ["-ddump-to-file", "-ddump-simpl", "-dsuppress-all"])
      runGhc (Just libdir) $ do
        dflags <- getSessionDynFlags
        let dflags' = gopt_set dflags Opt_BuildDynamicToo
        let dflags'' = dflags' { optLevel = 2 }
        setSessionDynFlags dflags''
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
