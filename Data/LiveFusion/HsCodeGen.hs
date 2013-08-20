-- Source Haskell code generator.
-- Most of the code is still in Combinators.hs but will migrate here SOON (c).

module Data.LiveFusion.HsCodeGen where

import Data.LiveFusion.Util
import Data.LiveFusion.Loop

import Data.Dynamic
import Data.Map as Map hiding ( map, filter )
import Data.List


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
