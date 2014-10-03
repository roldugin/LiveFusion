module Data.LiveFusion.Liveness where

import Data.LiveFusion.Loop
import Data.LiveFusion.Loop.Var
import Data.LiveFusion.Loop.Expr
import Data.LiveFusion.Util

import Data.Map ( Map )
import qualified Data.Map as Map
import Control.Category ( (>>>) )
import Data.List as List
import Data.Maybe


--------------------------------------------------------------------------------
-- * Environment

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
err_NOTDECLARED = "[Loop DSL Error] Attempt to assign to a variable that is not in scope: "
-- Maximum one assignment per block for now (TODO)
err_ASSIGNED = "[Loop DSL Error] Variable already assigned to in this block: "


emptyEnv = Env [] [] [] []


declare :: Var -> Env -> Env
declare v env
  | (v `elem` envDeclarations env) -- already declared
  = error (err_DECLARED ++ pprVar v)

  | otherwise
  = env { envDeclarations = v : envDeclarations env }


markEnvDirty :: Var -> Env -> Env
markEnvDirty v env
  | (v `elem` envDirty env)
  = error (err_ASSIGNED ++ pprVar v)

  | otherwise
  = env { envDirty = v : envDirty env }


assume :: Var -> Env -> Env
assume v env
  = env { envAssumptions = v : envAssumptions env }


assumeMany :: [Var] -> Env -> Env
assumeMany vars env = foldr assume env vars


-- | Lists the block as as potential next block to which control flow will be transferred
adoptBlock :: Label -> Env -> Env
adoptBlock lbl env
  = env { envNextBlocks = [lbl] `List.union` envNextBlocks env }


-- | Retrieves the free variables of an expression
varsE :: Expr -> [Var]
varsE (VarE v)   = [v]
varsE (AppE f x) = varsE f ++ varsE x
varsE (TermE _)  = [] -- DeBruijn Terms are closed
varsE (LitE _)   = [] -- Literals are constant terms


-- | Compute Environment for a block
--
-- Loops for:
-- + New variable declarations (declare)
-- + Variables assumed to be in scope (assume/assumeAllIn)
-- + Other blocks to which it is possible to jump from this block (adoptBlock)
-- + Variable mutations/updates (markEnvDirty)
--
-- Call to declare should come last to be more sure nothings is declared more than once.
blockEnv :: Block -> Env
blockEnv blk = postproc
             $ foldl (flip analyse) emptyEnv (blockStmts blk)
  where
    postproc env = env { envAssumptions = envAssumptions env \\ envDeclarations env }

    analyse :: Stmt -> Env -> Env
    analyse (Bind v e)     = assumeAllIn e >>> declare v
    analyse (Assign v e)   = assumeAllIn e >>> markEnvDirty v
    analyse (Case p lt lf) = assumeAllIn p >>> adoptBlock lt >>> adoptBlock lf
    analyse (Guard p lf)   = assumeAllIn p >>> adoptBlock lf
    analyse (Goto l)       = adoptBlock l
    analyse (NewArray arr n)        = assumeAllIn n >>> declare arr
    analyse (ReadArray x arr i)     = assume arr >>> assumeAllIn i >>> declare x
    analyse (WriteArray arr i x)    = assume arr >>> assumeAllIn i >>> assumeAllIn x
    analyse (ArrayLength x arr)     = assume arr >>> declare x
    analyse (SliceArray arr' arr n) = assume arr >>> assumeAllIn n >>> declare arr'
    analyse (Return v)     = assumeAllIn v

    assumeAllIn = assumeMany . varsE


-------------------------------------------------------------------------------
-- * VarMap

-- | Transitive environment assumptions
--
--   That is, all of the variables that will be required by the block with the
--   given label as well as any other block to where the control may end up.
--
--   This does not include variables that are bound by this of the future blocks.
--   These are conceptually all the free variables of the block and its futures.
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
                            (unsafeLoopEntry loop)
  where
    allLoopArgVars     = Map.keys $ loopArgs loop
    allLoopDecls       = concatMap (envDeclarations . blockEnv) (loopBlocks loop)
    allLoopAssumptions = concatMap (envAssumptions  . blockEnv) (loopBlocks loop)
    allBlockLocalVars  = (allLoopDecls `List.union` allLoopArgVars)
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


-- | Retrieves a block from the map. Like Map.! but with better error messages.
assumedVarsOfBlock :: Label -> VarMap -> [Var]
assumedVarsOfBlock lbl emap = fromMaybe err (Map.lookup lbl emap)
  where
    err = error
        $ "Label" +-+ pprLabel lbl +-+ "not in" +-+ pprVarMap emap



pprVarMap :: VarMap -> String
pprVarMap = ("Transitive Variable Map:" ++\)
          . unlines . map pprVarMapEntry . Map.assocs
  where
    pprVarMapEntry (lbl,vars) = pprLabel lbl ++ ": " ++ show vars
