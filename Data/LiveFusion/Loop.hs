{-# LANGUAGE GADTs, PatternGuards, StandaloneDeriving #-}

-- | Loop is a representation of a DSL with basic blocks
--   and explicit control flow using goto's.
--
--   It can be used for things other than loops since there is
--   no fixed loop structure but probably shouldn't.
--
--   The language offers statements for direct array manipulation.
module Data.LiveFusion.Loop
  ( module Data.LiveFusion.Loop
  , module Data.LiveFusion.Loop.Common
  , module Data.LiveFusion.Loop.LoopType
  , module Data.LiveFusion.Loop.Postprocess
  , module Data.LiveFusion.Loop.BlockMap
  , module Data.LiveFusion.Loop.Block
  , module Data.LiveFusion.Loop.Stmt
  , module Data.LiveFusion.Loop.Expr
  , module Data.LiveFusion.Loop.Label
  , module Data.LiveFusion.Loop.Var ) where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.LoopType
import Data.LiveFusion.Loop.Postprocess
import Data.LiveFusion.Loop.BlockMap
import Data.LiveFusion.Loop.Block
import Data.LiveFusion.Loop.Stmt
import Data.LiveFusion.Loop.Expr
import Data.LiveFusion.Loop.Label
import Data.LiveFusion.Loop.Var
