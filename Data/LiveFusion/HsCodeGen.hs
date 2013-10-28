{-# LANGUAGE TemplateHaskell #-}

-- Source Haskell code generator.
-- Most of the code is still in Combinators.hs but will migrate here SOON (c).

module Data.LiveFusion.HsCodeGen where

import Data.LiveFusion.Util
import Data.LiveFusion.Loop as Lp

import Language.Haskell.TH as TH

import Data.Dynamic
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.List

type VarList = Map Var Bool -- Dirty flag means that a variable has been updates in the given block

cgBlock :: VarList -> Block -> Dec
cgBlock vars (Block lbl stmts) = FunD (mkName lbl) [Clause pats body []]
  where
    pats = map (BangP . VarP . thName) (Map.keys vars) -- this relies keys being in order
    body = NormalB $ DoE thStmts
    (vars', thStmts) = mapAccumL stmt (clearVars vars) stmts


-- | Unsets dirty flag on al vars
clearVars :: VarList -> VarList
clearVars = Map.map (const False)

-- | Generates a TH statement from a statement in our repr.
--
-- Along the way it populates a map of used variables and their update status.
--
-- It is suitable to be used as an accumulating function to mapAccumL.
stmt :: VarList -> Lp.Stmt -> (VarList, TH.Stmt)
stmt vars (Bind v e)
  = let vars'  = insertFreshlyBound vars v
        (vars'', thExpr) = expr vars' e
        thVar  = VarP $ thName v
        thStmt = LetS [ValD thVar (NormalB thExpr) [{-no where clause-}]]
    in  (vars'', thStmt)
stmt vars (Assign v e)
  = let (vars', thExpr) = expr vars e
        vars'' = markDirty vars' v      -- the order matters, since expr expects v to be clean
                                        -- TODO: single update per block starts to sound like a bad idea now
        thVar  = VarP $ thDirtyName v
        thStmt = LetS [ValD thVar (NormalB thExpr) [{-no where clause-}]]
    in  (vars'', thStmt)
stmt vars (Case pred tLbl fLbl)
  = let (vars', thPredExp) = expr vars (Lp.VarE pred)
        thTExp = goto vars' tLbl
        thFExp = goto vars' fLbl
        thStmt = NoBindS $ CondE thPredExp thTExp thFExp
    in  (vars', thStmt)
stmt vars (Guard pred onFailLbl)
  = let (vars', thPredExp) = expr vars (Lp.VarE pred)
        thGotoExp = goto vars' onFailLbl
        unlessFn = TH.VarE $ mkName "Control.Monad.unless"
        thStmt = NoBindS $ TH.AppE (TH.AppE unlessFn thPredExp) thGotoExp
    in  (vars', thStmt)
stmt vars (Goto lbl)
  = let thStmt  = NoBindS $ goto vars lbl
    in  (vars, thStmt)

goto :: VarList -> Label -> TH.Exp
goto vars lbl = foldl TH.AppE fname args
  where
    fname = TH.VarE $ mkName lbl
    args  = map TH.VarE
          $ map toTHName
          $ Map.toList vars

    toTHName (v, False) = thName v
    toTHName (v, True)  = thDirtyName v


-- | Turn a Loop expression to a TH expression keeping an environment of seen variables.
--
-- TODO: This begs for an abstraction
expr :: VarList -> Lp.Expr -> (VarList, TH.Exp)
expr vars (Lp.VarE v)
  = let vars' = insertCheckClean vars v
        thExp = TH.VarE $ thName v
    in  (vars', thExp)
expr vars (Lp.App1 f v)
  = let (vars1, th_f) = expr vars  $ Lp.VarE f
        (vars2, th_v) = expr vars1 $ Lp.VarE v
        thExp = TH.AppE th_f th_v
    in  (vars2, thExp)
expr vars (Lp.App2 f v1 v2)
  = let (vars1, th_f)  = expr vars  $ Lp.VarE f
        (vars2, th_v1) = expr vars1 $ Lp.VarE v1
        (vars3, th_v2) = expr vars2 $ Lp.VarE v2
        thExp = TH.AppE (TH.AppE th_f th_v1) th_v2
    in  (vars3, thExp)
expr vars (Lp.App3 f v1 v2 v3)
  = let (vars1, th_f)  = expr vars  $ Lp.VarE f
        (vars2, th_v1) = expr vars1 $ Lp.VarE v1
        (vars3, th_v2) = expr vars2 $ Lp.VarE v2
        (vars4, th_v3) = expr vars3 $ Lp.VarE v3
        thExp = TH.AppE (TH.AppE (TH.AppE th_f th_v1) th_v2) th_v3
    in  (vars3, thExp)
expr vars (Lp.IntLit i)
  = let thExp = TH.LitE $ TH.IntegerL $ toInteger i
    in  (vars, thExp)


thName :: Lp.Var -> TH.Name
thName = TH.mkName . Lp.pprVar

thDirtyName :: Lp.Var -> TH.Name
thDirtyName = TH.mkName . (++ "'") . Lp.pprVar


-- | Can error out if the variable is already there
insertFreshlyBound :: VarList -> Var -> VarList
insertFreshlyBound vars v = Map.insertWith err v False vars
  where err _ _ = err_ALREADY_BOUND v


-- | The variable is either not present in the variable list or it's marked as clean.
--
-- Will error out if the variable is already dirty (has been assigned to)
insertCheckClean :: VarList -> Var -> VarList
insertCheckClean vars v = Map.insertWith err v False vars
  where err _ True = err_ALREADY_ASSIGNED v
        err d _ = d -- Supposedly False, i.e. Clean


markDirty :: VarList -> Var -> VarList
markDirty vars v
  = case (v `Map.member` vars) of
      True  -> Map.insertWith err v True vars
      False -> err_NOT_BOUND v
  where err _ True  = err_ALREADY_ASSIGNED v
        err d False = d -- Supposedly True, i.e. dirty


err_ALREADY_ASSIGNED v = error $
    "Attempted to use `" ++ pprVar v ++ "' which has been assigned to in this block."

err_ALREADY_BOUND v = error $
    "Attemped to bind `" ++ pprVar v ++ "' which was already bound elsewhere."

err_NOT_BOUND v = error $
    "Attempted to assign to `" ++ pprVar v ++ "' which has not been bound yet."


{-
pluginEntryCode :: String -> TypeRep -> Var -> Loop -> (String, [Arg])
pluginEntryCode entryFnName resultType resultVar loop
  = let code = entryFnName ++ " :: [Dynamic] -> Dynamic" ++\
               entryFnName `space` argsMatch ++\
               "  = toDyn $ runST $ loopST " ++ argsPass ++\
               " " ++\
               lSTCode
    in  (code, Map.elems pluginArgs)
  where
    pluginArgs = args loop
    argVars  = Map.keys pluginArgs
    lSTCode   = loopSTCode resultType resultVar loop
    argsMatch = showStringList $ map pprVar argVars  -- "[map_f1, arr2, ...]"
    argsPass  = juxtMap coerceArg argVars            -- "(fd map_f1) (fd arr2) ... "
    coerceArg = paren . ("fd "++) . pprVar            -- "(fd map_f1)"


loopSTCode :: TypeRep -> Var -> Loop -> String
loopSTCode resultTy resultVar (Loop args state binds guards len)
  = "loopST :: " ++ argsTypes ++ " -> ST s " ++ (paren $ show resultTy) ++\
    "loopST " ++ pluginArgsList ++ " ="     ++\
    "  do {"                          ++\
    "    dst  <- MV.new n"            ++:\  -- allocate an array of same size as the smallest input array
    "    len  <- loop dst 0 0"        ++:\  -- perform the traversal
    "    let { dst2 = MV.unsafeTake len dst }" ++:\  -- only take the filled portion of the result array
    "    dst3 <- V.unsafeFreeze dst2" ++:\  -- turn mutable array into immutable w/out copying
    "    return dst3 }" ++\
    "  where {" ++\
    "    n = " ++ (show len) ++:\
    "    loop " ++ loopArgsList ++ " =" ++\
    "      = let {" ++\
               indent 5 letsCode ++\
    "        } in " ++\
    "        do {" ++\
    "          guards" ++\
    "        }" ++:\
    "      False -> return o }}"
  where
    (argVars, argVals) = unzip $ Map.toList args
    argsTypes      = intercalate " -> "
                   $ map (paren . show . dynTypeRep) argVals
    pluginArgsList = intercalate " "
                   $ map pprVar argVars
    loopArgsList   = intercalate " "
                   $ map pprVar
                   $ map fst3 state
    letsCode       = intercalate ";\n"
                   $ concat [ stateUpdateCode state
                            , bindsCode binds
                            , guardsCode guards
                            , [skipCode]
                            , [yieldCode resultVar]
                            ]
    guardsCode'    = guardsCode guards
    fst3 (a,_,_)   = a

stateInitCode :: [(Var,Expr,Expr)] -> [String]
stateInitCode = map bind
  where
    bind (var,expr,_) = (pprVar var) ++ " <- " ++ (pprExpr expr)


--stateArgs :: [State] -> (String, Var)
--

stateUpdateCode :: [(Var,Expr,Expr)] -> [String]
stateUpdateCode map = []


skipCode :: String
skipCode = "skip = loop dst (i+1) o"


yieldCode :: Var -> String
yieldCode resultVar
  = "yield = do {" ++\
    "  MV.unsafeWrite dst o " ++ pprVar resultVar ++:\
    "  loop dst (i+1) (o+1) }"


guardsCode :: [(Expr,Var)] -> [String]
guardsCode guards
  = let (codes, first) = guardsCode' 1 guards
        entry = "guards = " ++ pprVar first -- `guard = yield' in case of no guards
    in  entry:codes
  where
    guardsCode' _ [] = ([], Var "yield")
    guardsCode' n (grd : rest)
      = let (codes, cont) = guardsCode' (n+1) rest
            label = Var $ "guard" ++ show n
            code  = guardCode label grd cont
        in  (code:codes, label)
    guardCode label (predicate,onfail) cont
      = pprVar label ++ " = case " ++ pprExpr predicate ++ " of " ++
        "{ False -> " ++ pprVar onfail ++ "; True -> " ++ pprVar cont ++ " }"


bindsCode :: (Map Var Expr) -> [String]
bindsCode = map bindCode . Map.toList
  where bindCode (var, expr) = (pprVar var) ++ " = " ++ (pprExpr expr)


--------------------------------------------------------------------------------
-- Expressions commonly used in loops ------------------------------------------

-- TODO: These should be independent of the code generation backend.

-- | Read an element from an array
readArrayExpr :: Var -> Var -> Expr
readArrayExpr arr ix = App2 reader arr ix
  where reader = Var "readArray"


-- | Write an element to an array
writeArrayExpr :: Var -> Var -> Var -> Expr
writeArrayExpr arr ix elt = App3 writer arr ix elt
  where writer = Var "writeArray"


ltExpr :: Var -> Var -> Expr
ltExpr a b = App2 op a b
  where op = Var "(<)"


newArrayExpr :: Var -> Expr
newArrayExpr len = App1 allocator len
  where allocator = Var "newArray"


incrExpr :: Var -> Expr
incrExpr var = App1 incr var
  where incr = Var "increment"


--------------------------------------------------------------------------------
-- Code templates --------------------------------------------------------------

preamble :: String -> String
preamble moduleName =
  "module " ++ moduleName ++ " where                                       " ++\
  "import Data.Vector.Unboxed as V                                         " ++\
  "import Data.Vector.Unboxed.Mutable as MV                                " ++\
  "import Unsafe.Coerce                                                    " ++\
  "import Data.Dynamic                                                     " ++\
  "import GHC.Prim (Any)                                                   " ++\
  "import Control.Monad.ST                                                 " ++\
  "                                                                        " ++\
  "fd :: Typeable a => Dynamic -> a                                        " ++\
  "fd d = case fromDynamic d of                                            " ++\
  "         Just v  -> v                                                   " ++\
  "         Nothing -> error \"Argument type mismatch\"                    " ++\
  "                                                                        " ++\
  "increment :: Int -> Int                                                 " ++\
  "increment = (+1)                                                        " ++\
  "                                                                        " ++\
  "readArray :: Unbox a => V.Vector a -> Int -> a                          " ++\
  "readArray arr i = V.unsafeIndex arr ix                                  " ++\
  "                                                                        " ++\
  "writeArray :: Unbox a => MV.MVector s a -> Int -> a -> ST s ()          " ++\
  "writeArray arr i x = MV.unsafeWrite arr i x                             " ++\
  "                                                                        " ++\
  "newArray :: Unbox a => Int -> ST (MV.MVector s a)                       " ++\
  "newArray n = MV.new n                                                   " ++\
  "                                                                        "
-}