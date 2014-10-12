module Data.LiveFusion.Loop.Block where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.Stmt
import Data.LiveFusion.Loop.Label
import Data.LiveFusion.Loop.Var

import Data.LiveFusion.DisjointSet

import Data.Functor
import Data.Maybe
import Data.Set ( Set )
import qualified Data.Set as Set

import Control.Applicative ( (<|>) )


data Block = Block [Stmt] (Maybe Stmt)


emptyBlock :: Block
emptyBlock = Block [] Nothing


blockBodyStmts :: Block -> [Stmt]
blockBodyStmts (Block stmts _) = stmts


blockFinalStmt :: Block -> Maybe Stmt
blockFinalStmt (Block _ final) = final


blockStmts :: Block -> [Stmt]
blockStmts (Block stmts final) = stmts ++ maybeToList final


addStmtsToBlock :: [Stmt] -> Block -> Block
addStmtsToBlock stmts (Block stmts0 final0) = Block (stmts0 ++ stmts) final0


-- | Replace all statements in the block.
--
-- Note that this keeps the final statement intact.
setStmtsOfBlock :: [Stmt] -> Block -> Block
setStmtsOfBlock stmts (Block _ final0) = Block stmts final0


setBlockFinal :: Stmt -> Block -> Block
setBlockFinal final = setBlockFinalMb (Just final)


setBlockFinalMb :: Maybe Stmt -> Block -> Block
setBlockFinalMb final (Block stmts _) = Block stmts final


unsetBlockFinal :: Block -> Block
unsetBlockFinal (Block stmts _) = Block stmts Nothing


mergeBlocks :: Block -> Block -> Block
mergeBlocks (Block stmts1 final1) (Block stmts2 final2)
  = Block (stmts1 ++ stmts2) (final1 <|> final2)


class BlockContainer c where
  mapBlocks :: (Block -> Block) -> c -> c

instance VarContainer Block where
  mapVars f = mapStmts (mapVars f)

instance StmtContainer Block where
  mapStmts f (Block stmts final) = Block (map f stmts) (f <$> final)

instance LabelContainer Block where
  mapLabels f (Block stmts final) = let f' = mapLabels f
                                    in  Block (map f' stmts) (f' <$> final)


pprBlock :: Block -> String
pprBlock (Block stmts mbfinal)
  = unlines $ map pprStmt (stmts ++ fin)
  where fin = maybe [] return mbfinal -- returns either singleton or empty list


rewriteBlockLabelsAndRates :: [Set Label] -> IntDisjointSet -> Block -> Block
rewriteBlockLabelsAndRates lbls rates (Block stmts final) = Block stmts' final'
  where
    stmts' = map (rewriteStmtRates rates)
           $ map (rewriteStmtLabels lbls)
           $ stmts
    final' = rewriteStmtRates rates
         <$> rewriteStmtLabels lbls
         <$> final


-------------------------------------------------------------------------------
-- * Transfering statements between blocks


