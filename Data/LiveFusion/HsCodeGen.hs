{-# LANGUAGE TemplateHaskell #-}

-- Source Haskell code generator.

module Data.LiveFusion.HsCodeGen where

import Data.LiveFusion.Util
import Data.LiveFusion.Loop as Lp

import Language.Haskell.TH as TH

import Data.Dynamic
import Data.Map ( Map, (!) )
import qualified Data.Map as Map
import Data.List

-- | Generate a TH function represeting a code block of a loop.
--
--   TODO: Perhaps passing the whole environment is not the best approach.
--   TODO: KNOWN ISSUE Updated variable cannot be used in the same block.
cgBlock :: VarMap -> Block -> Dec
cgBlock emap blk@(Block lbl stmts) = blockFun
  where
    blockFun = FunD (mkName lbl) [Clause pats body []]
    pats = map (BangP . VarP . thName) blockArgs
    body = NormalB $ DoE thStmts
    thStmts = map (toTHStmt emap dirtyVars) stmts

    blockArgs = emap ! lbl

    -- Variables that are updated in this block
    dirtyVars = envDirty (blockEnv blk)


-- | Generates a TH statement from a statement in our Loop representation.
toTHStmt :: VarMap -> [Var] -> Lp.Stmt -> TH.Stmt
toTHStmt _ _ (Bind v e)
  = let thExp = toTHExp e
        thVar  = VarP $ thName v
        thStmt = LetS [ValD thVar (NormalB thExp) [{-no where clause-}]]
    in  thStmt

toTHStmt _ _ (Assign v e)
  = let thExp = toTHExp e
        thVar  = VarP $ thDirtyName v
        thStmt = LetS [ValD thVar (NormalB thExp) [{-no where clause-}]]
    in  thStmt

toTHStmt emap dirtyVars (Case pred tLbl fLbl)
  = let thPredExp = toTHExp (Lp.VarE pred)
        thTExp = goto emap dirtyVars tLbl
        thFExp = goto emap dirtyVars fLbl
        thStmt = NoBindS $ CondE thPredExp thTExp thFExp
    in  thStmt

toTHStmt emap dirtyVars (Guard pred onFailLbl)
  = let thPredExp = toTHExp (Lp.VarE pred)
        thGotoExp = goto emap dirtyVars onFailLbl
        unlessFn = TH.VarE $ mkName "Control.Monad.unless"
        thStmt = NoBindS $ TH.AppE (TH.AppE unlessFn thPredExp) thGotoExp
    in  thStmt

toTHStmt emap dirtyVars (Goto lbl)
  = NoBindS $ goto emap dirtyVars lbl


goto :: VarMap -> [Var] -> Label -> TH.Exp
goto emap dirtyVars lbl = foldl TH.AppE thFName thArgs
  where
    args    = emap ! lbl

    thFName = TH.VarE $ mkName lbl

    thArgs  = map TH.VarE
            $ map toTHName
            $ args

    toTHName v | v `elem` dirtyVars = thDirtyName v
               | otherwise          = thName v


-- | Turn a Loop toTHExpession to a TH toTHExpession.
--
toTHExp :: Lp.Expr -> TH.Exp
toTHExp (Lp.VarE v)
  = toTHVarE v

toTHExp (Lp.App1 f v)
  = let th_f = toTHVarE f
        th_v = toTHVarE v
    in  TH.AppE th_f th_v

toTHExp (Lp.App2 f v1 v2)
  = let th_f  = toTHVarE f
        th_v1 = toTHVarE v1
        th_v2 = toTHVarE v2
    in  TH.AppE (TH.AppE th_f th_v1) th_v2

toTHExp (Lp.App3 f v1 v2 v3)
  = let th_f  = toTHVarE f
        th_v1 = toTHVarE v1
        th_v2 = toTHVarE v2
        th_v3 = toTHVarE v3
    in  TH.AppE (TH.AppE (TH.AppE th_f th_v1) th_v2) th_v3

toTHExp (Lp.IntLit i)
  = TH.LitE $ TH.IntegerL $ toInteger i


-- | Perhaps one day we will support Exprs in more places.
--   For now much of our loop language are just Vars.
toTHVarE :: Lp.Var -> TH.Exp
toTHVarE = TH.VarE . thName

thName :: Lp.Var -> TH.Name
thName = TH.mkName . Lp.pprVar


thDirtyName :: Lp.Var -> TH.Name
thDirtyName = TH.mkName . (++ "'") . Lp.pprVar


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

stateInitCode :: [(Var,ToTHExp,ToTHExp)] -> [String]
stateInitCode = map bind
  where
    bind (var,toTHExp,_) = (pprVar var) ++ " <- " ++ (pprToTHExp toTHExp)


--stateArgs :: [State] -> (String, Var)
--

stateUpdateCode :: [(Var,ToTHExp,ToTHExp)] -> [String]
stateUpdateCode map = []


skipCode :: String
skipCode = "skip = loop dst (i+1) o"


yieldCode :: Var -> String
yieldCode resultVar
  = "yield = do {" ++\
    "  MV.unsafeWrite dst o " ++ pprVar resultVar ++:\
    "  loop dst (i+1) (o+1) }"


guardsCode :: [(ToTHExp,Var)] -> [String]
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
      = pprVar label ++ " = case " ++ pprToTHExp predicate ++ " of " ++
        "{ False -> " ++ pprVar onfail ++ "; True -> " ++ pprVar cont ++ " }"


bindsCode :: (Map Var ToTHExp) -> [String]
bindsCode = map bindCode . Map.toList
  where bindCode (var, toTHExp) = (pprVar var) ++ " = " ++ (pprToTHExp toTHExp)


--------------------------------------------------------------------------------
-- ToTHExpessions commonly used in loops ------------------------------------------

-- TODO: These should be independent of the code generation backend.

-- | Read an element from an array
readArrayToTHExp :: Var -> Var -> ToTHExp
readArrayToTHExp arr ix = App2 reader arr ix
  where reader = Var "readArray"


-- | Write an element to an array
writeArrayToTHExp :: Var -> Var -> Var -> ToTHExp
writeArrayToTHExp arr ix elt = App3 writer arr ix elt
  where writer = Var "writeArray"


ltToTHExp :: Var -> Var -> ToTHExp
ltToTHExp a b = App2 op a b
  where op = Var "(<)"


newArrayToTHExp :: Var -> ToTHExp
newArrayToTHExp len = App1 allocator len
  where allocator = Var "newArray"


incrToTHExp :: Var -> ToTHExp
incrToTHExp var = App1 incr var
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