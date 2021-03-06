module Data.LiveFusion.Loop.Stmt where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.Expr
import Data.LiveFusion.Loop.Label
import Data.LiveFusion.Loop.Var

import Data.LiveFusion.Scalar.HOAS as HOAS

import Data.LiveFusion.AliasMap
import Data.LiveFusion.DisjointSet as Rates
import Data.LiveFusion.Util

import Data.List as List
import Data.Maybe
import Data.Set ( Set )
import qualified Data.Set as Set

import Prelude as P


data Stmt = Bind   Var Expr
          | Assign Var Expr
          | Case   Expr Label Label
          | Guard  Expr Label
          | Goto   Label
          | Return [Var]
          -- Array statements.
          -- They are here because some of them are stateful operations
          -- and they are backend specific.
          -- Perhaps there is a cleaner way to do this.
          | NewArray    Var  {- Array name -}
                        Expr {- Array length -}
          | ReadArray   Var  {- Variable to read into -}
                        Var  {- Array name -}
                        Expr {- Index -}
          | WriteArray  Var  {- Array name -}
                        Expr {- Index -}
                        Expr {- Element -}
          | ArrayLength Var  {- Variable to bind to -}
                        Var  {- Array name -}
          | SliceArray  Var  {- New array name (TODO: ugly) -}
                        Var  {- Array name -}
                        Expr {- Array length -}


bindStmt     = Bind
assignStmt   = Assign
caseStmt     = Case
guardStmt    = Guard
gotoStmt     = Goto
returnStmt   = Return
newArrStmt   = NewArray
readArrStmt  = ReadArray
writeArrStmt = WriteArray
arrLenStmt   = ArrayLength
sliceArrStmt = SliceArray


instance VarContainer Stmt where
  mapVars f stmt = go stmt
   where
    go (Bind v e) = Bind (f v) (mapVars f e)
    go (Assign v e) = Assign (f v) (mapVars f e)
    go (Case e l1 l2) = Case (mapVars f e) l1 l2
    go (Guard e l) = Guard (mapVars f e) l
    go (Goto l) = Goto l
    go (Return vs) = Return (P.map f vs)
    go (NewArray v e) = NewArray (f v) (mapVars f e)
    go (ReadArray v1 v2 e) = ReadArray (f v1) (f v2) (mapVars f e)
    go (WriteArray v ei ex) = WriteArray (f v) (mapVars f ei) (mapVars f ex)
    go (ArrayLength v1 v2) = ArrayLength (f v1) (f v2)
    go (SliceArray v1 v2 e) = SliceArray (f v1) (f v2) (mapVars f e)

instance LabelContainer Stmt where
  mapLabels f = go
   where
    go (Case e l1 l2) = Case e (f l1) (f l2)
    go (Guard e l) = Guard e (f l)
    go (Goto l) = Goto (f l)
    go s_ = s_

instance Analyse Stmt where
  binds = maybeToList . bindsMb
  references = go
   where
    go (Bind _ e)   = references e
    go (Assign _ e) = references e
    go (Case e _ _) = references e
    go (Guard e _)  = references e
    go (Goto _)     = []
    go (Return vs)  = vs

    go (NewArray _ e)       = references e
    go (ReadArray _ v e)    = v : references e
    go (WriteArray v ei ex) = v : references ei
                               ++ references ex
    go (ArrayLength _ v)    = [v]
    go (SliceArray _ v e)   = v : references e


class StmtContainer c where
  mapStmts :: (Stmt -> Stmt) -> c -> c


bindsMb :: Stmt -> Maybe Var
bindsMb = go
  where
    go (Bind v _) = Just v
    {-
    go (Assign v e)
    go (Case e l1 l2)
    go (Guard e l)
    go (Goto l)
    go (Return e)
    -}
    go (NewArray v _) = Just v
    go (ReadArray v _ _) = Just v
    {-
    go (WriteArray v ei ex)
    -}
    go (ArrayLength v _) = Just v
    go (SliceArray v _ _) = Just v
    go _ = Nothing


-- | Dependency order of two statements.
--
-- Currently two statements are equal if they:
-- 
--   * don't depend on each other, and
--
--   * either both bind a variable
--
--   * or both don't bind a variable
--
-- The equality is in terms of where to place the statement.
-- This is different from complete equality of even /clashing/
-- where two statements bind the same variable. See @clash@.
orderStmts :: Stmt -> Stmt -> Ordering
orderStmts s1 s2 = ord mbv1 mbv2
 where
  ord Nothing   Nothing   = EQ  -- No dep since they don't bind vars
  ord (Just v1) Nothing   = LT  -- Binding statements have precedence
  ord Nothing   (Just v2) = GT  -- ^^^
  ord (Just v1) (Just v2)       -- Both statements are binding:
    | v1 `elem` refs2 = LT      --  * s2 depends on s1
    | v2 `elem` refs1 = GT      --  * s1 depends on s2
    | otherwise       = EQ      --  * neither

  -- *Maybe* they bind variables
  mbv1  = bindsMb s1
  mbv2  = bindsMb s2
  
  -- Variables they reference  
  refs1 = references s1
  refs2 = references s2

{- PROBLEM with `sortBy orderStmtms`:
Partial ordering does not seem to work properly because we use EQ Ordering
to mean there's no dependence relation between two statements.

In particualar the map is the following breaks it and stuff doesn't compile:
bpermute (map (+1) [0,1,2,3,4,5,6,7,8,9]) [3,2,6,8,5,3]

Sorting the following does nothing:
C := B                           B := A
D := C    = should produce =>    C := B
B := A                           D := C
-}


-------------------------------------------------------------------------------
-- * Pretty printing

instance Show Stmt where
  show = pprStmt


pprStmt :: Stmt -> String
pprStmt (Bind v e)     = "let" +-+ pprVar v +-+ "=" +-+ pprExpr e
pprStmt (Assign v e)   = pprVar v +-+ ":=" +-+ pprExpr e
pprStmt (Guard p l)    = "unless" +-+ pprExpr p +-+ "|" +-+ pprLabel l
pprStmt (Case p l1 l2) = "if" +-+ pprExpr p +-+ "|" +-+ pprLabel l1 +-+ pprLabel l2
pprStmt (Goto l)       = "goto" +-+ pprLabel l
pprStmt (NewArray arr n)        = "let" +-+ pprVar arr +-+ "= newArray" +-+ pprExpr n
pprStmt (ReadArray x arr i)     = "let" +-+ pprVar x +-+ "= readArray" +-+ pprVar arr +-+ pprExpr i
pprStmt (WriteArray arr i x)    = "writeArray" +-+ pprVar arr +-+ pprExpr i +-+ pprExpr x
pprStmt (ArrayLength i arr)     = "let" +-+ pprVar i +-+ "= arrayLength" +-+ pprVar arr
pprStmt (SliceArray arr' arr n) = "let" +-+ pprVar arr' +-+ "= sliceArray" +-+ pprVar arr +-+ pprExpr n
pprStmt (Return vs)    = "return" +-+ (paren $ intercalateMap ", " pprVar vs)



-------------------------------------------------------------------------------
-- * Fancy stuff

-- | Splits a list of statements to those required to define the given @Var@
--   and the rest.
extractWithDeps :: Var -> [Stmt] -> ([Stmt],[Stmt])
extractWithDeps v = extract [v]
  where
    extract vs stmts
      = let -- find statements that bind vs
            (found, rest) = partition (bindsAny vs) stmts
            -- find all variables those statements reference
            moreDeps = concatMap references found
            -- find statements that bind those
            (moreFound, rest') = extract moreDeps rest
        in  if null found then (found, rest)
                          else (found ++ moreFound, rest')

    bindsAny vs stmt = case bindsMb stmt of
                         Just v  -> v `elem` vs
                         Nothing -> False


-------------------------------------------------------------------------------
-- * Loop specific

-- | Similar to @rewriteStmtLabels@ but rewrites index variables
--
-- TODO: Matching on variable name is ugly.
rewriteStmtRates :: IntDisjointSet -> Stmt -> Stmt
rewriteStmtRates rates = mapVars rw
  where
    rw v@(Var prefix uq)
      | prefix == indexPrefix
      = indexVar (Rates.representative uq rates)
      | otherwise
      = v
    rw v_ = v_


-- | In the final loop we choose just one label out of all
--   and use it everywhere where the same set of labels is used.
--
-- For example
-- @
-- body_3:
-- body_2:
--   elt_3 = f elt_2
--   goto yield_3
-- @
-- gets rewritten to use the smallest label
-- @
-- body_3:
-- body_2:
--   elt_3 = f elt_2
--   goto yield_2    <-- changed
-- @
rewriteStmtLabels :: [Set Label] -> Stmt -> Stmt
rewriteStmtLabels lbls = mapLabels rw
  where
    rw l = theSynonymLabel lbls l


-- | Two statement are considered to be clashing if they bind the same variable.
clash :: Stmt -> Stmt -> Bool
clash (Bind v1 _) (Bind v2 _) = v1 == v2
clash (Assign v1 _) (Assign v2 _) = v1 == v2
clash (Case p1 t1 f1) (Case p2 t2 f2) = (p1 ==? p1) && (t1 == t2) && (f1 == f2)
clash (Guard p1 l1) (Guard p2 l2) = (p1 ==? p2) && (l1 == l2)
clash (Goto l1) (Goto l2) = l1 == l2
clash (Return _) (Return _) = True  -- perhaps this could be relaxed
clash (NewArray v1 _) (NewArray v2 _) = v1 == v2
clash (ReadArray v1 _ _) (ReadArray v2 _ _) = v1 == v2
clash (WriteArray v1 _ _) (WriteArray v2 _ _) = v1 == v2
clash (ArrayLength v1 _) (ArrayLength v2 _) = v1 == v2
clash (SliceArray v1 _ _) (SliceArray v2 _ _) = v1 == v2
clash _ _ = False -- Although two expressions binding the same variable should technically clash.



-------------------------------------------------------------------------------
-- * Noise

incStmt :: Var -> Stmt
incStmt v = assignStmt v incExpr
  where
    incExpr  = plusIntE `AppE` vE `AppE` oneE
    plusIntE = TermE (lam2 plusInt)
    vE       = varE v
