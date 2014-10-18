{-# LANGUAGE GADTs, RankNTypes, DeriveDataTypeable, ScopedTypeVariables, ExplicitForAll #-}
module Data.LiveFusion.Evaluator where

import Data.LiveFusion.AST
import Data.LiveFusion.Loop as Loop
import Data.LiveFusion.Util
import Data.LiveFusion.Types hiding ( Unique )
import Data.LiveFusion.Scalar.HOAS as HOAS
import Data.LiveFusion.Fuse
import Data.LiveFusion.Sharing

-- TODO We should not hardcode HsBackend here
import Data.LiveFusion.HsBackend

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


-- | Evaluates the AST to a final value.
evalAST :: Typeable a => AST a -> a
evalAST (Manifest vec) = vec
evalAST ast = result
  where
    loop = getLoop ast
    dynResult = evalLoop loop (typeOf result)
    result = fromJust $ fromDynamic dynResult
{-# NOINLINE evalAST #-}


getLoop :: Typeable a => AST a -> Loop
getLoop = postprocessLoop . unsafePerformIO . fuseToLoop
{-# NOINLINE getLoop #-}


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
