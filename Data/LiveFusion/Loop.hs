{-# LANGUAGE GADTs #-}

-- | Loop is an abstract representation of a loop computation.
--   It can be used to generate loop code.

module Data.LiveFusion.Loop where

import Data.LiveFusion.Util

import Data.Map ( Map )
import qualified Data.Map as Map
import Data.Dynamic
import Data.List as List
import Data.Monoid
import Control.Monad
import Control.Category ( (>>>) )


type Id = Int

type Name  = String

data Var = IdVar Name Id
         | SimplVar Name
  deriving ( Eq, Ord )

instance Show Var where
  show = pprVar

var :: Name -> Id -> Var
var = IdVar

eltVar :: Id -> Var
eltVar = var "elt"

indexVar :: Id -> Var
indexVar = var "ix"

ltFn = SimplVar "(<)"
plusFn = SimplVar "(+)"
lengthFn = SimplVar "length"
readFn = SimplVar "unsafeIndex"

type Arg   = Dynamic

data Block = Block Label [Stmt]

blockStmts :: Block -> [Stmt]
blockStmts (Block _ stmts) = stmts

type Label = String

data Stmt = Bind Var Expr
          | Assign Var Expr
          | Case Var Label Label
          | Guard Var Label
          | Goto Label

bindStmt = Bind
assignStmt = Assign
caseStmt = Case
guardStmt = Guard
gotoStmt = Goto

data Loop = Loop { -- | Global arguments and their values
                   loopArgs   :: (Map Var Arg)

                   -- | List of requested manifest arrays
                 , loopResults    :: [Var]

                   -- | List of goto code loopBlockMap
                 , loopBlockMap :: BlockMap
                 }


type BlockMap = Map Label Block


loopBlocks :: Loop -> [Block]
loopBlocks = Map.elems . loopBlockMap


updateBlock :: Label -> (Block -> Block) -> Loop -> Loop
updateBlock lbl mut loop = putBlock block' loop
  where
    block  = getBlock lbl loop
    block' = mut block


getBlock :: Label -> Loop -> Block
getBlock lbl loop = maybe emptyBlock id maybeBlock
  where
    blockMap  = loopBlockMap loop
    maybeBlock = Map.lookup lbl blockMap
    emptyBlock = Block lbl []


putBlock :: Block -> Loop -> Loop
putBlock blk@(Block lbl _) loop = loop { loopBlockMap = loopBlockMap' }
  where
    loopBlockMap' = Map.insert lbl blk (loopBlockMap loop)


addStmtsToBlock :: [Stmt] -> Block -> Block
addStmtsToBlock stmts (Block lbl stmts0) = Block lbl (stmts0 ++ stmts)


-- Append a statement to the specified code block
addStmt :: Stmt -> Label -> Loop -> Loop
addStmt stmt lbl = updateBlock lbl (addStmtsToBlock [stmt])


addStmts :: [Stmt] -> Label -> Loop -> Loop
addStmts stmts lbl = updateBlock lbl (addStmtsToBlock stmts)


pprBlockMap :: BlockMap -> String
pprBlockMap = concatMap pprBlock . Map.elems


pprBlock :: Block -> String
pprBlock (Block lbl stmts)
  = pprLabel lbl ++ ":" ++\
    (indent 1 $ unlines $ map pprStmt stmts)


pprStmt :: Stmt -> String
pprStmt (Bind v e)     = "let " ++ pprVar v ++ " = " ++ pprExpr e
pprStmt (Assign v e)   = pprVar v ++ " := " ++ pprExpr e
pprStmt (Guard v l)    = "guard on " ++ pprVar v ++ " | onFail: " ++ pprLabel l
pprStmt (Case p l1 l2) = "if " ++ pprVar p ++
                         " then " ++ pprLabel l1 ++
                         " else " ++ pprLabel l2
pprStmt (Goto l)       = "goto " ++ pprLabel l


pprLabel :: Label -> String
pprLabel = id


instance Show Loop where
  show (Loop loopArgs loopResults loopBlockMap)
    = "Loop LoopArgs:   " ++ (show $ Map.keys loopArgs) ++\
      "     LoopResults:    " ++ show loopResults ++\
      "     LoopBlockMap: " ++\ pprBlockMap loopBlockMap


addArg var arg loop = loop { loopArgs = loopArgs' }
  where loopArgs' = Map.insert var arg (loopArgs loop)


addLoopResults arrVar loop = loop { loopResults = loopResults' }
  where loopResults' = arrVar : (loopResults loop)


-- | Several predefined labels
initLbl :: Label
initLbl = "init"

guardLbl :: Label
guardLbl = "guard"

--readLbl :: Label
--readLbl = "read"

bodyLbl :: Label
bodyLbl = "body"

bottomLbl :: Label
bottomLbl = "bottom"

doneLbl :: Label
doneLbl = "done"


-- | Per block environment which tracks the variables that the block
--   relies upon being present, the variables declared in this block as well as
--   variables that have been destructively assigned to in this block.
--
--   The environment can be used to compute the arguments to the block when presenting
--   it as pure function as well as detect programming errors of the DSL program.
--
data Env = Env { -- | Variables expected to be in environment
                 envAssumptions :: [Var]

                 -- | Newly declared variables
               , envDeclarations :: [Var]

                 -- | Variables that have been assigned to
               , envDirty :: [Var]

                 -- | LoopBlockMap to which control flow may be transferred
               , envNextBlocks :: [Label]
               }


err_DECLARED = "[Loop DSL Error] Variable already declared in the environment: "
err_NOTDECLARED = "[Loop DSL Error] Attmpt to assign to a variable that is not in scope: "
-- Maximum one assignment per block for now (TODO)
err_ASSIGNED = "[Loop DSL Error] Variable already assigned to in this block: "

{-
instance Monoid Env where
  mempty = Env [] [] []
  mappend (Env ass1 decl1 envDirty1) (Env ass2 decl2 envDirty2) = Env ass decl envDirty
    where
      ass   = (ass1 \\ decl) `List.union` (ass2 \\ decl) -- TODO: Ugly. Forcibly disjoins vars
                                                         -- assumed from prev loopBlockMap and
                                                         -- declared in the current block
      decl  = if null bad@(common [decl1, decl2, ass1, ass2])
                 then decl1 ++ decl2
                 else die err_DECLARED bad
      envDirty = disjointCheck err_ASSIGNED envDirty1 envDirty2 -- TODO: probably also wanna check the var
                                                       -- has been declared
      disjointCheck errString xs ys
            = let badVars = xs `intersect` ys
              in  if List.null badVars
                     then xs ++ ys
                     else die errString badVars
                          -- This is a crude way to fail, however there is no easy
                          -- static way to check this. Besides, the DSL is internal
                          -- to the library so it should not fail if everything is
                          -- implemented right.
      die errString badVars = error $ errString ++ show badVars
-}


emptyEnv = Env [] [] [] []


declare :: Var -> Env -> Env
declare v env
  | (v `elem` envAssumptions env) || (v `elem` envDeclarations env) -- already declared
  = error (err_DECLARED ++ pprVar v)

  | otherwise
  = env { envDeclarations = v : envDeclarations env }


markEnvDirty :: Var -> Env -> Env
markEnvDirty v env
  | (v `notElem` envAssumptions env) && (v `notElem` envDeclarations env)
  = error (err_NOTDECLARED ++ pprVar v)

  | (v `elem` envDirty env)
  = error (err_ASSIGNED ++ pprVar v)

  | otherwise
  = env { envDirty = v : envDirty env }


assume :: Var -> Env -> Env
assume v env
  | (v `elem` envDeclarations env) || (v `elem` envAssumptions env) -- already assumed (or declared)
  = env

  | otherwise
  = env { envAssumptions = v : envAssumptions env }


assumeMany :: [Var] -> Env -> Env
assumeMany vars env = foldr assume env vars


-- | Lists the block as as potentian next block to which control flow will be transferred
adoptBlock :: Label -> Env -> Env
adoptBlock lbl env
  = env { envNextBlocks = [lbl] `union` envNextBlocks env }


-- | Retrieves the free variables of an expression
varsE :: Expr -> [Var]
varsE (VarE v) = [v]
varsE (App1 f v) = [f, v]
varsE (App2 f v1 v2) = [f, v1, v2]
varsE (App3 f v1 v2 v3) = [f, v1, v2, v3]
varsE (IntLit _) = []


blockEnv :: Block -> Env
blockEnv blk = foldl (flip analyse) emptyEnv (blockStmts blk)
  where
    analyse :: Stmt -> Env -> Env
    analyse (Bind v e)     = assumeMany (varsE e) >>> declare v
    analyse (Assign v e)   = assumeMany (varsE e) >>> markEnvDirty v
    analyse (Case v lt lf) = assume v >>> adoptBlock lt >>> adoptBlock lf
    analyse (Guard p lf)   = assume p >>> adoptBlock lf
    analyse (Goto l)       = adoptBlock l


-- | Transitive environment envAssumptions
type VarMap = Map Label [Var]


-- | A simpler replacement of liveness analysis. Computes a maximal set of variables
--   that may be required by the block and its futures.
--
--   The liveness analysis as such only applies to variables that are never used outside
--   the block they are declared in.
extendedEnv :: Loop -> VarMap
extendedEnv loop = purgeBlockLocalVars
                 $ traceEnv allLoopArgVars -- all declarations so far
                            Map.empty
                            initLbl        -- init is assumed to be the entry block
  where
    allLoopArgVars     = Map.keys $ loopArgs loop
    allLoopDecls       = concatMap (envDeclarations . blockEnv) (loopBlocks loop)
    allLoopAssumptions = concatMap (envAssumptions  . blockEnv) (loopBlocks loop)
    allBlockLocalVars  = (allLoopDecls `union` allLoopArgVars)
                       \\ allLoopAssumptions

    purgeBlockLocalVars :: VarMap -> VarMap
    purgeBlockLocalVars = Map.map (\\ allBlockLocalVars)

    traceEnv :: [Var] -> VarMap -> Label -> VarMap
    traceEnv pastDecls emap currLbl
      | currLbl `Map.member` emap  -- Cycle detected - stop
      = emap

      | otherwise
      = let assms = envAssumptions env  -- environment assumptions of current block

            partialMap = Map.insert currLbl pastDecls emap -- insert all available declarations
                                                           -- as requirements for this block

            env        = blockEnv (getBlock currLbl loop)  -- this block's environment

            partialDecls = pastDecls ++ envDeclarations env  -- all known declarations
                                                             -- including this block's ones

            nextLbls   = envNextBlocks env   -- all possible next blocks

            -- Merge environments of past and future blocks.
            -- NOTE: If a block pops up multiple times it means there are multiple paths to
            --       it in the control flow graph. Use only those declarations that all
            --       paths can provide.
            resultMap = foldl (Map.unionWith List.intersect)
                        partialMap                 -- extended environment of this and past blocks
                      $ map (traceEnv partialDecls partialMap)  -- assumptions of future blocks
                      $ nextLbls

        in  resultMap


pprVarMap :: VarMap -> String
pprVarMap = ("Transitive Variable Map:" ++\)
          . unlines . map pprVarMapEntry . Map.assocs
  where
    pprVarMapEntry (lbl,vars) = lbl ++ ": " ++ show vars


-- | Inserts known Gotos between several of the predefined blocks
postprocessLoop :: Loop -> Loop
postprocessLoop
  = addStmt (gotoStmt guardLbl)  initLbl    -- Init -> Guard
  . addStmt (gotoStmt bodyLbl)   guardLbl   -- Guard -> Body
  . addStmt (gotoStmt bottomLbl) bodyLbl    -- Body -> Bottom
  . addStmt (gotoStmt guardLbl)  bottomLbl  -- Bottom -> Guard


-- Guard which causes the end of loop on failure (like break)
--addExitGuard cond = addGuard cond (Var "done") -- TODO: add a common set of labels

-- Guard which skips iteration on failure (like continue)
--addSkipGuard cond = addGuard cond (Var "skip")

-- A guard with the specified condition and the failure label
--addGuard cond onfail loop = loop { guards = guards' }
--  where guards' = (guards loop) `List.union` [(cond, onfail)] -- guards are ordered


--setLen n loop = loop { len = len' }
--  where curr  = len loop
--        len'  | curr == 0  = n
--              | otherwise = n `min` curr


instance Monoid Loop where
  mempty = Loop Map.empty [] Map.empty
  mappend loop1 loop2
    = Loop { loopArgs    = loopArgs    `joinBy` Map.union
           , loopResults = loopResults `joinBy` List.union
           , loopBlockMap  = loopBlockMap  `joinBy` Map.unionWith appendLoopBlockMap
           }
    where
      joinBy :: (Loop  -> field)          -- field to take from loop
             -> (field -> field -> field) -- joining function
             -> field                    -- new field
      field `joinBy` f = f (field loop1) (field loop2)


append :: Loop -> Loop -> Loop
append = mappend


empty :: Loop
empty = mempty


appendLoopBlockMap :: Block -> Block -> Block
appendLoopBlockMap (Block lbl stmts1) (Block _ stmts2)
  = Block lbl (stmts1 ++ stmts2)

-- | Represents an expression in the loop.
--
--   NOTE: It would be difficult to type the expression tree as `Expr a'
--         as we would no longer be able to easily construct collections
--         of such expressions, e.g.:
--   > [Expr Int, Expr Double, Expr Double]
--
--   Thoughts:
--   1. One way to keep the types would be to keep a TypeRep inside each Var.
--
--   2. Alternatively we could minimise the use of data structures such as lists
--   and maps and instead keep more stuff in the tree itself.
data Expr where
  VarE   :: Var -> Expr
  App1   :: Var -> Var -> Expr
  App2   :: Var -> Var -> Var -> Expr
  App3   :: Var -> Var -> Var -> Var -> Expr
  IntLit :: Int -> Expr
  deriving ( Show, Eq )


pprExpr :: Expr -> String
pprExpr (VarE v)
  = pprVar v
pprExpr (App1 f x)
  = pprVar f `space` pprVar x
pprExpr (App2 f x y)
  = pprVar f `space` pprVar x `space` pprVar y
pprExpr (App3 f x y z)
  = pprVar f `space` pprVar x `space`
    pprVar y `space` pprVar z
pprExpr (IntLit i)
  = show i


pprName :: Name -> String
pprName = id


pprVar :: Var -> String
pprVar (IdVar name ident) = pprName name ++ "_" ++ pprId ident
pprVar (SimplVar name) = pprName name

pprId :: Id -> String
pprId = show

-- | Create a new variable from a the given one
--prime :: Var -> Var
--prime (Var name ident) = Var $ name ++ "'"