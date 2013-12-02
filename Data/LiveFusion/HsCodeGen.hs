{-# LANGUAGE TemplateHaskell #-}

-- Source Haskell code generator.

module Data.LiveFusion.HsCodeGen where

import Data.LiveFusion.Util
import Data.LiveFusion.Loop as Lp
import qualified Data.LiveFusion.FuzzyMap as FMap

import Language.Haskell.TH as TH

import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.List
import Data.Functor.Identity
import System.IO.Unsafe ( unsafePerformIO )
import Control.Arrow ( first )

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
cgBlock :: VarMap -> Label -> Block -> Dec
cgBlock emap lbl blk@(Block stmts final) = blockFun
  where
    blockFun = FunD (cgLabelName lbl) [Clause pats fnBody []]
    pats = map (BangP . VarP . cgVarName) blockArgs
    fnBody = NormalB $ DoE (cgStmts stmts)

    cgStmts (stmt:rest)
      = case stmt of
          (Guard p lbl) -> return {- a sinleton list -}
                        $ cgGuardStmt emap dirtyVars   -- environment stuff
                                      p    lbl         -- guard parameters
                                      (cgStmts rest) -- statements following the guard
          _             -> (cgStmt emap dirtyVars stmt) : (cgStmts rest)
    cgStmts [] = []

    blockArgs = emap ! lbl

    -- Variables that are updated in this block
    dirtyVars = envDirty (blockEnv blk)


cgLabelName :: Label -> TH.Name
cgLabelName = mkName . pprLabel

-- | Guard is a little tricky because we have queue up the statement after
--   the the block into one of the branches.
--
--   TODO: If creating new blocks was easier in our framework, we could potentially
--   generate a whole new block for the rest of the statements and generalise the Guard
--   to a Case expression.
cgGuardStmt :: VarMap -> [Var] -> Var -> Label -> [TH.Stmt] -> TH.Stmt
cgGuardStmt emap dirtyVars pred onFailLbl followingStmts
  = let thPredExp = cgExp (Lp.VarE pred)
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

cgStmt emap dirtyVars (Case pred tLbl fLbl)
  = let thPredExp = cgExp (Lp.VarE pred)
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
        len = cgVar n
    in  thStmt

cgStmt _ _ (WriteArray arr i x)
  = let thStmt = NoBindS $ TH.AppE (TH.AppE (TH.AppE writeArrayFn arr_th) i_th) x_th
        writeArrayFn = TH.VarE $ mkName "writeArray"
        arr_th = cgVar arr
        i_th   = cgVar i
        x_th   = cgVar x
    in  thStmt

cgStmt _ _ (SliceArray arr' arr n)
  = let thStmt = BindS (BangP $ VarP $ cgVarName arr')
                       (TH.AppE (TH.AppE sliceArrayFn arr_th) n_th)
        sliceArrayFn = TH.VarE $ mkName "sliceArray"
        arr_th = cgVar arr
        n_th   = cgVar n
    in  thStmt

cgStmt _ _ (Return v)
  = let thStmt   = NoBindS $ TH.AppE returnFn v_th
        returnFn = TH.VarE $ mkName "return"
        v_th     = cgVar v
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

-- | Turn a Loop cgExpession to a TH cgExpession.
--
cgExp :: Lp.Expr -> TH.Exp
cgExp (Lp.VarE v)
  = cgVar v

cgExp (Lp.App1 f v)
  = let th_f = cgVar f
        th_v = cgVar v
    in  TH.AppE th_f th_v

cgExp (Lp.App2 f v1 v2)
  = let th_f  = cgVar f
        th_v1 = cgVar v1
        th_v2 = cgVar v2
    in  TH.AppE (TH.AppE th_f th_v1) th_v2

cgExp (Lp.App3 f v1 v2 v3)
  = let th_f  = cgVar f
        th_v1 = cgVar v1
        th_v2 = cgVar v2
        th_v3 = cgVar v3
    in  TH.AppE (TH.AppE (TH.AppE th_f th_v1) th_v2) th_v3

cgExp (Lp.IntLit i)
  = TH.LitE $ TH.IntegerL $ toInteger i


-- | Perhaps one day we will support Exprs in more places.
--   For now much of our loop language are just Vars.
cgVar :: Lp.Var -> TH.Exp
cgVar = TH.VarE . cgVarName

cgVarName :: Lp.Var -> TH.Name
cgVarName = TH.mkName . Lp.pprVar


cgDirtyVarName :: Lp.Var -> TH.Name
cgDirtyVarName = TH.mkName . (++ "'") . Lp.pprVar


defaultPluginCode :: Loop -> String
defaultPluginCode = pluginCode "Plugin" "entry"


pluginCode :: String -> String -> Loop -> String
pluginCode moduleName entryFnName loop
  = preamble moduleName              ++\
    pluginEntryCode entryFnName loop ++\
    loopCode loop


pluginEntryCode :: String -> Loop -> String
pluginEntryCode entryFnName loop
  = pprint [fnSig, fnDefn]
  where
    fnSig     = SigD fnName fnTy
    fnDefn    = FunD fnName [Clause [argList] (NormalB loopCall) []]

    fnName    = mkName entryFnName         -- E.g. entry_

    fnTy      = dynListTy `to` dynTy       -- [Dynamic] -> Dynamic

    dynTy     = ConT $ mkName "Dynamic"    -- [Dynamic]
    dynListTy = AppT ListT dynTy           -- Dynamic

    -- | Makes a type for (ty1 -> ty2)
    to :: Type -> Type -> Type
    ty1 `to` ty2 = AppT (AppT ArrowT ty1) ty2

    -- [!f1, !f2, !arr1, ...]
    argList   = ListP
              $ map (BangP . VarP . cgVarName) argVars

    -- (fd f1) (fd f2) (fd arr1) ...
    loopCall  = toDynamic
              $ applyMany loopEntry
              $ map (coerceArg . TH.VarE . cgVarName) argVars

    -- Applies the arg to fd function (fromDynamic, expected to be in scope)
    coerceArg = AppE (TH.VarE $ mkName "fd")

    toDynamic = AppE (TH.VarE $ mkName "toDyn")

    -- E.g. init_
    loopEntry = TH.VarE $ cgLabelName $ unsafeLoopEntry loop

    argVars   = Map.keys $ loopArgs loop



loopCode :: Loop -> String
loopCode loop = pprint
              $ map codeGenBlock allBlocks
  where
    codeGenBlock (lbl,blk) = cgBlock extEnv lbl blk

    allBlocks = map (first theOneLabel) (FMap.assocs $ loopBlockMap loop)

    extEnv    = extendedEnv loop -- Environment after variable and goto analyses


--------------------------------------------------------------------------------
-- Code templates --------------------------------------------------------------

preamble :: String -> String
preamble moduleName =
  "{-# LANGUAGE BangPatterns #-}                                           " ++\
  "module " ++ moduleName ++ " where                                       " ++\
  "                                                                        " ++\
  "import Data.Vector.Unboxed as V                                         " ++\
  "import Data.Vector.Unboxed.Mutable as MV                                " ++\
  "import Unsafe.Coerce                                                    " ++\
  "import Data.Dynamic                                                     " ++\
  "import GHC.Prim (Any)                                                   " ++\
  "import Control.Monad.ST                                                 " ++\
  "import Control.Monad.Primitive                                          " ++\
  "                                                                        " ++\
  "fd :: Typeable a => Dynamic -> a                                        " ++\
  "fd d = case fromDynamic d of                                            " ++\
  "         Just v  -> v                                                   " ++\
  "         Nothing -> error \"Argument type mismatch\"                    " ++\
  "                                                                        " ++\
  "lengthArray :: Unbox a => V.Vector a -> Int                             " ++\
  "lengthArray = V.length                                                  " ++\
  "                                                                        " ++\
  "readArray :: V.Unbox a => Int -> V.Vector a -> a                        " ++\
  "readArray i arr = V.unsafeIndex arr i                                   " ++\
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