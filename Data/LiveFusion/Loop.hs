{-# LANGUAGE GADTs #-}

-- | Loop is an abstract representation of a loop computation.
--   It can be used to generate loop code.

module Data.LiveFusion.Loop where

import Data.LiveFusion.Util

import Data.Map as Map hiding ( map )
import Data.Dynamic
import Data.List as List
import Data.Monoid

type Id = Int

type Name  = String

data Var = IdVar Name Id
         | SimplVar Name
  deriving ( Show, Eq, Ord )

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
                   args   :: (Map Var Arg)

                   -- | List of requested manifest arrays
                 , out    :: [Var]

                   -- | List of goto code blocks
                 , blocks :: BlockMap
                 }

type BlockMap = Map Label Block

updateBlock :: Label -> (Block -> Block) -> Loop -> Loop
updateBlock lbl mut loop = putBlock block' loop
  where
    block  = getBlock lbl loop
    block' = mut block

getBlock :: Label -> Loop -> Block
getBlock lbl loop = maybe emptyBlock id maybeBlock
  where
    blockMap = blocks loop
    maybeBlock = Map.lookup lbl blockMap
    emptyBlock = Block lbl []

putBlock :: Block -> Loop -> Loop
putBlock blk@(Block lbl _) loop = loop { blocks = blocks' }
  where
    blocks' = Map.insert lbl blk (blocks loop)

addStmtsToBlock :: [Stmt] -> Block -> Block
addStmtsToBlock stmts (Block lbl stmts0) = Block lbl (stmts0 ++ stmts)

-- Append a statement to the specified code block
addStmt :: Stmt -> Label -> Loop -> Loop
addStmt stmt lbl = updateBlock lbl (addStmtsToBlock [stmt])

addStmts :: [Stmt] -> Label -> Loop -> Loop
addStmts stmts lbl = updateBlock lbl (addStmtsToBlock stmts)

pprBlockMap :: BlockMap -> String
pprBlockMap = concatMap pprBlock . elems

pprBlock :: Block -> String
pprBlock (Block lbl stmts)
  = pprLabel lbl ++ ":" ++\
    (indent 1 $ unlines $ map pprStmt stmts)

pprStmt :: Stmt -> String
pprStmt (Bind v e)     = "let " ++ pprVar v ++ " = " ++ pprExpr e
pprStmt (Assign v e)   = pprVar v ++ " := " ++ pprExpr e
pprStmt (Guard v l)    = "guard " ++ pprVar v ++ " onFail " ++ pprLabel l
pprStmt (Case p l1 l2) = "if " ++ pprVar p ++
                         " then " ++ pprLabel l1 ++
                         " else " ++ pprLabel l2
pprStmt (Goto l)       = "goto " ++ pprLabel l

pprLabel :: Label -> String
pprLabel = id

instance Show Loop where
  show (Loop args out blocks)
    = "Loop Args:   " ++ (show $ map pprVar $ Map.keys args) ++\
      "     Out:    " ++ show out ++\
      "     Blocks: " ++\ pprBlockMap blocks


addArg var arg loop = loop { args = args' }
  where args' = Map.insert var arg (args loop)


addOut arrVar loop = loop { out = out' }
  where out' = arrVar : (out loop)


-- | Several predefined labels
initLbl :: Label
initLbl = "init"

guardLbl :: Label
guardLbl = "guard"

readLbl :: Label
readLbl = "read"

bodyLbl :: Label
bodyLbl = "body"

bottomLbl :: Label
bottomLbl = "bottom"

doneLbl :: Label
doneLbl = "done"


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
    = Loop { args   = args   `joinBy` Map.union
           , out    = out    `joinBy` List.union
           , blocks = blocks `joinBy` Map.unionWith appendBlocks
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


appendBlocks :: Block -> Block -> Block
appendBlocks (Block lbl stmts1) (Block _ stmts2)
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