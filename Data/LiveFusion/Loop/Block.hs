module Data.LiveFusion.Loop.Block where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.Stmt
import Data.LiveFusion.Loop.Label
import Data.LiveFusion.Loop.Var

import Data.Functor
import Data.Maybe


data Block = Block [Stmt] (Maybe Stmt)


emptyBlock :: Block
emptyBlock = Block [] Nothing


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
setBlockFinal final (Block stmts _) = Block stmts (Just final)


unsetBlockFinal :: Block -> Block
unsetBlockFinal (Block stmts _) = Block stmts Nothing


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
