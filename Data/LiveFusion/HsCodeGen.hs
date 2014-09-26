{-# LANGUAGE TemplateHaskell, GADTs #-}

-- Source Haskell code generator.

module Data.LiveFusion.HsCodeGen where

import Data.LiveFusion.HsBackend
import Data.LiveFusion.HsBackend.Types

import qualified Data.LiveFusion.Scalar.HOAS as HOAS
import Data.LiveFusion.Scalar.DeBruijn as DeBruijn
import Data.LiveFusion.Scalar.Convert as DeBruijn

import Data.LiveFusion.Util
import Data.LiveFusion.Types
import Data.LiveFusion.Loop as Lp
import qualified Data.LiveFusion.AliasMap as AMap

import Language.Haskell.TH as TH

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.List
import Data.Functor.Identity
import System.IO.Unsafe ( unsafePerformIO )
import Control.Arrow ( first )
import Data.Maybe
import Data.Char

-- Modules required for code generation
import qualified Data.Vector.Unboxed as V
import qualified Data.Vector.Unboxed.Mutable as MV
import Control.Monad.ST.Strict
import Control.Monad.Primitive
import Data.Dynamic


-- | Generate a TH function represeting a code block of a loop.
--
--   TODO: Perhaps passing the whole environment is not the best approach.
--   TODO: KNOWN ISSUE Updated variable cannot be used in the same block.
cgBlock :: VarMap -> Label -> Block -> TH.Dec
cgBlock emap lbl blk = blockFun
  where
    -- A function representing a block of statements in the loop, e.g. body_1 ... = do { ... }
    blockFun = FunD (cgLabelName lbl) [Clause pats fnBody []]
    pats = map (BangP . VarP . cgVarName) blockArgs
    fnBody = NormalB $ DoE (cgStmts $ blockStmts blk)

    cgStmts (stmt:rest)
      = case stmt of
          (Guard p lbl) -> return {- a sinleton list -}
                        $ cgGuardStmt emap dirtyVars   -- environment stuff
                                      p    lbl         -- guard parameters
                                      (cgStmts rest)   -- statements following the guard
          _             -> (cgStmt emap dirtyVars stmt) : (cgStmts rest)
    cgStmts [] = []


    blockArgs = emap ! lbl

    -- Variables that are updated in this block
    dirtyVars = envDirty (blockEnv blk)


cgLabelName :: Label -> TH.Name
cgLabelName = mkName . pprLabel

-- | Guard is a little tricky because we have to queue up the statement after
--   the statement into one of the branches.
--
--   TODO: If creating new blocks was easier in our framework, we could potentially
--   generate a whole new block for the rest of the statements and generalise the Guard
--   to a Case expression.
cgGuardStmt :: VarMap -> [Var] -> Expr -> Label -> [TH.Stmt] -> TH.Stmt
cgGuardStmt emap dirtyVars predE onFailLbl followingStmts
  = let thPredExp = cgExp predE
        thcgGotoExpExp = cgGotoExp emap dirtyVars onFailLbl
        thOKExp   = DoE followingStmts
        thStmt    = NoBindS $ TH.CondE thPredExp thOKExp thcgGotoExpExp
    in  thStmt


-- | Generates a TH statement from a statement in our Loop representation.
cgStmt :: VarMap -> [Var] -> Lp.Stmt -> TH.Stmt
cgStmt _ _ (Bind v e)
  = let thExp  = cgExp e
        thVar  = BangP $ VarP $ cgVarName v
        thStmt = LetS [ValD thVar (NormalB thExp) [{-no where clause-}]]
    in  thStmt

cgStmt _ _ (Assign v e)
  = let thExp  = cgExp e
        thVar  = BangP $ VarP $ cgDirtyVarName v
        thStmt = LetS [ValD thVar (NormalB thExp) [{-no where clause-}]]
    in  thStmt

cgStmt emap dirtyVars (Case predE tLbl fLbl)
  = let thPredExp = cgExp predE
        thTExp = cgGotoExp emap dirtyVars tLbl
        thFExp = cgGotoExp emap dirtyVars fLbl
        thStmt = NoBindS $ CondE thPredExp thTExp thFExp
    in  thStmt

cgStmt emap dirtyVars (Goto lbl)
  = NoBindS $ cgGotoExp emap dirtyVars lbl

cgStmt _ _ (NewArray arr n)
  = let thStmt = BindS (BangP $ VarP $ cgVarName arr)
                       (TH.AppE newArrayFn len)
        newArrayFn = TH.VarE $ mkName "newArray"
        len = cgExp n
    in  thStmt

cgStmt _ _ (ReadArray x arr i)
  = let thStmt = LetS [ValD lhs (NormalB rhs) [{-no where clause-}]]

        lhs = BangP $ VarP $ cgVarName x
        rhs = (TH.AppE (TH.AppE readArrayFn arr_th) i_th)

        readArrayFn = TH.VarE $ mkName "readArray"
        arr_th = cgVar arr
        i_th   = cgExp i

    in  thStmt

cgStmt _ _ (WriteArray arr i x)
  = let thStmt = NoBindS $ TH.AppE (TH.AppE (TH.AppE writeArrayFn arr_th) i_th) x_th
        writeArrayFn = TH.VarE $ mkName "writeArray"
        arr_th = cgVar arr
        i_th   = cgExp i
        x_th   = cgExp x
    in  thStmt

cgStmt _ _ (SliceArray arr' arr n)
  = let thStmt = BindS (BangP $ VarP $ cgVarName arr')
                       (TH.AppE (TH.AppE sliceArrayFn arr_th) n_th)
        sliceArrayFn = TH.VarE $ mkName "sliceArray"
        arr_th = cgVar arr
        n_th   = cgExp n
    in  thStmt

cgStmt _ _ (Return v)
  = let thStmt   = NoBindS $ TH.AppE returnFn v_th
        returnFn = TH.VarE $ mkName "return"
        v_th     = cgExp v
    in  thStmt



cgGotoExp :: VarMap -> [Var] -> Label -> TH.Exp
cgGotoExp emap dirtyVars lbl = applyMany thFName thArgs
  where
    args    = emap ! lbl

    thFName = TH.VarE $ cgLabelName lbl

    thArgs  = map (TH.VarE . cgArg) args

    cgArg v | v `elem` dirtyVars = cgDirtyVarName v
            | otherwise          = cgVarName v


-- | Takes a list of expressions and applies them one after the other
applyMany1 :: [TH.Exp] -> TH.Exp
applyMany1 [] = error "applyMany: Nothing to apply"
applyMany1 exps = foldl1 TH.AppE exps

applyMany :: TH.Exp -> [TH.Exp] -> TH.Exp
applyMany fun exps = applyMany1 (fun : exps)


-- | Turn a Loop Language Expession to a TH Expression.
--
cgExp :: Lp.Expr -> TH.Exp
cgExp (Lp.VarE v)
  = cgVar v

cgExp (Lp.AppE f x)
  = let th_f = cgExp f
        th_x = cgExp x
    in  TH.AppE th_f th_x

cgExp (Lp.TermE term)
  = cgHOAS term

cgExp (Lp.LitE e)
  = cgElt e


cgHOAS :: (Typeable t) => HOAS.Term t -> TH.Exp
cgHOAS = cgDeBruijn . convertSharing


-- This uses unsafePerformIO because the rest of code generation happens
-- outside of Q monad. This is probably not a great idea, so it will have
-- to be rewritten soon (or never :))
cgDeBruijn :: Typeable t => DeBruijn.Term env t -> TH.Exp
cgDeBruijn = cg (-1)
  where
    cg :: Int -> DeBruijn.Term env t -> TH.Exp
    {-# NOINLINE cg #-}
    cg lvl (Var ix)
      = TH.VarE $ thName lvl ix

    cg lvl (CodeT code)
      = unsafePerformIO $ runQ $ fromMaybe err (getTH code)
      where err = error "cgDeBruijn: No TH implementation provided"

    cg lvl (Con c)
      = error "cgDeBruijn: Con unsupported"

    cg lvl (Lam body)
      = TH.LamE [TH.VarP (thName (lvl + 1) ZeroIdx)] (cg (lvl + 1) body)

    cg lvl (App fun arg)
      = TH.AppE (cg lvl fun) (cg lvl arg)

    cg lvl (Let bnd body)
      = error "cgDeBruijn: Let binding unsupported"

    thName :: Int -> Idx env t -> TH.Name
    thName lvl ix = TH.mkName $ pprIdx lvl ix

    pprIdx :: Int -> Idx env t -> String
    pprIdx lvl idx
      | n < 26    = [chr (ord 'a' + n)]
      | otherwise = 'v':show n
      where
        n = lvl - idxToInt idx



-- | Perhaps one day we will support Exprs in more places.
--   For now much of our loop language are just Vars.
cgVar :: Lp.Var -> TH.Exp
cgVar = TH.VarE . cgVarName

cgVarName :: Lp.Var -> TH.Name
cgVarName = TH.mkName . Lp.pprVar


cgDirtyVarName :: Lp.Var -> TH.Name
cgDirtyVarName = TH.mkName . (++ "'") . Lp.pprVar


defaultPluginCode :: Loop -> TypeRep -> String
defaultPluginCode = pluginCode "Plugin" "entry"


pluginCode :: String -> String -> Loop -> TypeRep -> String
pluginCode moduleName entryFnName loop resultTy
  = preamble moduleName                       ++\
    pluginEntryCode entryFnName loop resultTy ++\
    loopCode loop


pluginEntryCode :: String -> Loop -> TypeRep -> String
pluginEntryCode entryFnName loop resultTy
  = pprint
  $ pluginEntryCodeTH entryFnName loop resultTy


pluginEntryCodeTH :: String -> Loop -> TypeRep -> [TH.Dec]
pluginEntryCodeTH entryFnName loop resultTy
  = [dyntyEntrySig, dyntyEntryDec, tyEntrySig, tyEntryDec]
  where
    -- Make dynamically typed entry into the plugin like entry_Plugin1234 :: [Dynamic] -> Dynamic
    dyntyEntrySig  = SigD dyntyEntryName dyntyEntryTy
    dyntyEntryDec  = FunD dyntyEntryName [Clause [argList] (NormalB tyEntryCall) []]

    dyntyEntryName = mkName entryFnName     -- E.g. entry_Plugin1234

    dyntyEntryTy   = dynListTy `to` dynTy   -- [Dynamic] -> Dynamic

    dynTy          = ConT $ mkName "Dynamic"    -- [Dynamic]
    dynListTy      = AppT ListT dynTy           -- Dynamic

    -- [!f1, !f2, !arr1, ...]
    argList        = ListP argPats
    argPats        = map (BangP . VarP . cgVarName) argVars

    -- toDyn (entry (fd f1) (fd f2) (fd arr1) ... )
    tyEntryCall    = toDynamicE
                   $ applyMany (TH.VarE tyEntryName)
                   $ map (coerceArgE . TH.VarE . cgVarName) argVars


    -- Make statically typed entry into the plugin like entry :: Vector Double -> Vector Int -> Vector Double
    tyEntrySig     = SigD tyEntryName tyEntryTy
    tyEntryDec     = FunD tyEntryName [Clause argPats (NormalB loopCall) []]

    tyEntryTy      = foldr to (thTypeRepTy resultTy)
                   $ map (thTypeRepTy . dynTypeRep) argVals

    loopCall       = runSTE
                   $ applyMany loopEntry
                   $ map (TH.VarE . cgVarName) argVars

    -- | Makes a type for (ty1 -> ty2)
    to :: Type -> Type -> Type
    ty1 `to` ty2 = AppT (AppT ArrowT ty1) ty2

    -- Applies the arg to fd function (fromDynamic, expected to be in scope)
    coerceArgE = TH.AppE (TH.VarE $ mkName "fd")

    toDynamicE = TH.AppE (TH.VarE $ mkName "toDyn")

    runSTE     = TH.AppE (TH.VarE $ mkName "runST")

    -- E.g. run
    tyEntryName   = TH.mkName "run"

    -- E.g. init_
    loopEntry = TH.VarE $ cgLabelName $ unsafeLoopEntry loop

    argVars   = Map.keys  $ loopArgs loop
    argVals   = Map.elems $ loopArgs loop


thTypeOf :: Typeable a => a -> TH.Type
thTypeOf = thTypeRepTy . typeOf


-- | Convert TypeRep representation to TemplateHaskell's Type
--
-- It may or may not work with function, tuples and list types.
-- However it will convert Int, Vector Int and Vector (Vector Double).
thTypeRepTy :: TypeRep -> TH.Type
thTypeRepTy rep 
  = foldl AppT
          (tyConType tyCon) 
  $ map thTypeRepTy tyArgs
  where
    (tyCon, tyArgs) = splitTyConApp rep

    tyConType :: TyCon -> TH.Type
    tyConType = ConT . TH.mkName . show


loopDecs :: Loop -> [TH.Dec]
loopDecs loop = map codeGenBlock allBlocks
  where
    codeGenBlock (lbl,blk) = cgBlock extEnv lbl blk

    allBlocks = map (first theOneLabel) (AMap.assocs $ loopBlockMap loop)

    extEnv    = extendedEnv loop -- Environment after variable and goto analyses


loopCode :: Loop -> String
loopCode = pprint . loopDecs


--------------------------------------------------------------------------------
-- Code templates --------------------------------------------------------------

preamble :: String -> String
preamble moduleName =
  "{-# LANGUAGE BangPatterns #-}                                           " ++\
  "module " ++ moduleName ++ " ( entry_" ++ moduleName ++ " ) where        " ++\
  "                                                                        " ++\
  "import Data.Vector.Unboxed as V                                         " ++\
  "import Data.Vector.Unboxed.Mutable as MV                                " ++\
  "import Unsafe.Coerce                                                    " ++\
  "import Data.Dynamic                                                     " ++\
  "import Data.Ratio                                                       " ++\
  "import GHC.Prim (Any)                                                   " ++\
  "import GHC.Num                                                          " ++\
  "import GHC.Real                                                         " ++\  
  "import GHC.Classes                                                      " ++\
  "import Control.Monad.ST                                                 " ++\
  "import Control.Monad.Primitive                                          " ++\
  "import Data.Tuple                                                       " ++\
  "                                                                        " ++\
  "fd :: Typeable a => Dynamic -> a                                        " ++\
  "fd d = case fromDynamic d of                                            " ++\
  "         Just v  -> v                                                   " ++\
  "         Nothing -> error \"Argument type mismatch\"                    " ++\
  "                                                                        " ++\
  "arrayLength :: Unbox a => V.Vector a -> Int                             " ++\
  "arrayLength = V.length                                                  " ++\
  "                                                                        " ++\
  "readArray :: V.Unbox a => V.Vector a -> Int -> a                        " ++\
  "readArray = V.unsafeIndex                                               " ++\
  "                                                                        " ++\
  "writeArray :: V.Unbox a => MV.MVector s a -> Int -> a -> ST s ()        " ++\
  "writeArray arr i x = MV.unsafeWrite arr i x                             " ++\
  "                                                                        " ++\
  "newArray :: V.Unbox a => Int -> ST s (MV.MVector s a)                   " ++\
  "newArray n = MV.new n                                                   " ++\
  "                                                                        " ++\
  "sliceArray :: (V.Unbox a, PrimMonad m) => MV.MVector (PrimState m) a -> Int -> m (V.Vector a) " ++\
  "sliceArray vec len = V.unsafeFreeze $ MV.unsafeTake len vec             " ++\
  "                                                                        "


-- The following generates fresh names, so avoid TH for now...
{-
helperFunctions :: [Dec]
helperFunctions = unsafePerformIO $ runQ [d|

  fd :: Typeable a => Dynamic -> a
  fd d = case fromDynamic d of
           Just v  -> v
           Nothing -> error "Argument type mismatch"

  lengthArray :: Unbox a => V.Vector a -> Int
  lengthArray = V.length

  readArray :: V.Unbox a => Int -> V.Vector a -> a
  readArray i arr = V.unsafeIndex arr i

  writeArray :: V.Unbox a => MV.MVector s a -> Int -> a -> ST s ()
  writeArray arr i x = MV.unsafeWrite arr i x

  newArray :: V.Unbox a => Int -> ST s (MV.MVector s a)
  newArray n = MV.new n

  sliceArray :: (V.Unbox a, PrimMonad m) => MV.MVector (PrimState m) a -> Int -> m (V.Vector a)
  sliceArray vec len = V.unsafeFreeze $ MV.unsafeTake len vec

  |]
{-# NOINLINE helperFunctions #-}
-}
