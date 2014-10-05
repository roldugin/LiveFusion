module Data.LiveFusion.Loop.LoopType where

import Data.LiveFusion.Loop.Common
import Data.LiveFusion.Loop.BlockMap
import Data.LiveFusion.Loop.Block
import Data.LiveFusion.Loop.Stmt
import Data.LiveFusion.Loop.Label
import Data.LiveFusion.Loop.Var

import Data.LiveFusion.Util
import Data.LiveFusion.AliasMap ( AliasMap )
import Data.LiveFusion.DisjointSet as Rates
import qualified Data.LiveFusion.AliasMap as AMap


import Data.Maybe
import Data.Map ( Map )
import qualified Data.Map as Map

import Data.Set ( Set )
import qualified Data.Set as Set

import Data.Dynamic
import Data.List as List
import Data.Monoid
import Control.Applicative ( (<|>) )


data Loop = Loop { -- | Loop entry block
                   loopEntry        :: Maybe Label

                   -- | Global arguments and their values
                 , loopArgs         :: (Map Var Arg)

                   -- | Resulting manifest array
                 , loopArrResult    :: Maybe Id  -- May not be the best way to represent this,
                                                 -- but currently the easiest.

                   -- | Resulting scalar result
                 , loopScalarResult :: Maybe Var


                   -- | The id of the loop whose @yield@ block produces the elements
                 , loopTheRate      :: Maybe Unique


                   -- | All the different rates of the loop, unified
                 , loopRates        :: IntDisjointSet


                   -- | For segmented array operations: Just (segd_uq, data_uq)
                 , loopNest         :: Maybe (Unique, Unique)


                   -- | Guard tests and index initialisation/increments that need *not* be inserted
                 , loopSkipTests    :: [Unique]  -- These are for the postprocessing step
                 , loopSkipIncrs    :: [Unique]  -- and should probably be dealt with more elegantly.


                   -- | Loop's basic blocks with their associated labels
                 , loopBlockMap     :: BlockMap
                 }



-------------------------------------------------------------------------------
-- * Pretty printing

instance Show Loop where
  show = pprLoop

pprLoop :: Loop -> String
pprLoop loop
  = "Loop Entry:    "  ++  maybe "None" pprLabel (loopEntry loop)                   ++\
    "Loop Args:     "  ++  (show $ Map.keys $ loopArgs loop)                        ++\
    "Array Result:  "  ++  maybe "None" (pprVar . arrayVar) (loopArrResult loop)    ++\
    "Scalar Result: "  ++  maybe "None" pprVar              (loopScalarResult loop) ++\
    "The rate:      "  ++  maybe "None" pprId               (loopTheRate loop)      ++\
    "Rates:         "  ++  pprDisjointSet (loopRates loop)                          ++\
    "Nesting:       "  ++  maybe "None" pprNest             (loopNest loop)         ++\
    "Skip inserting:" ++\
    "  Inits/Incrs: "  ++  show (loopSkipIncrs loop)                                ++\
    "  Tests:       "  ++  show (loopSkipTests loop)                                ++\
    "BlockMap:      "  ++\ pprBlockMap (loopBlockMap loop)
  where
    pprNest (s,d) = "(segd " ++ pprId s ++ ", data " ++ pprId d ++ ")"



-------------------------------------------------------------------------------
-- * Merging loops

instance Monoid Loop where
  mempty
    = Loop { loopEntry        = Nothing
           , loopArgs         = Map.empty
           , loopArrResult    = Nothing
           , loopScalarResult = Nothing
           , loopTheRate      = Nothing
           , loopRates        = Rates.empty
           , loopNest         = Nothing
           , loopSkipIncrs    = []
           , loopSkipTests    = []
           , loopBlockMap     = AMap.empty
           }
  mappend loop1 loop2
    = Loop { loopEntry        = loopEntry     `joinWith` (<|>)
           , loopArgs         = loopArgs      `joinWith` Map.union
           , loopArrResult    = Nothing
           , loopScalarResult = Nothing
           , loopTheRate      = loopTheRate   `joinWith` (<|>)
           , loopRates        = loopRates     `joinWith` Rates.merge
           , loopNest         = loopNest      `joinWith` (<|>)
           , loopSkipIncrs    = loopSkipIncrs `joinWith` (++)
           , loopSkipTests    = loopSkipTests `joinWith` (++)
           , loopBlockMap     = loopBlockMap  `joinWith` AMap.unionWith mergeBlocks
           }
    where
      joinWith :: (Loop  -> field)          -- field to take from loop
               -> (field -> field -> field) -- joining function
               -> field                     -- new field
      field `joinWith` f = f (field loop1) (field loop2)


append :: Loop -> Loop -> Loop
append = mappend


emptyLoop :: Loop
emptyLoop = mempty



-------------------------------------------------------------------------------
-- * Loop block management

loopBlocks :: Loop -> [Block]
loopBlocks = AMap.elems . loopBlockMap


updateBlock :: Label -> (Block -> Block) -> Loop -> Loop
updateBlock lbl f loop = putBlock lbl block' loop
  where
    block  = getBlock lbl loop
    block' = f block


-- | Retrieves an existing block out of the loop or returns and empty block
getBlock :: Label -> Loop -> Block
getBlock lbl loop = fromMaybe emptyBlock maybeBlock
  where
    maybeBlock = AMap.lookup lbl (loopBlockMap loop)


putBlock :: Label -> Block -> Loop -> Loop
putBlock lbl blk loop = loop { loopBlockMap = loopBlockMap' }
  where
    loopBlockMap' = AMap.insert lbl blk (loopBlockMap loop)


-- | Removes all statements from block (excluding final)
clearBlock :: Label -> Loop -> Loop
clearBlock = replaceStmts []


-- | Sets the final statement of a given block to be goto to another block
setFinalGoto :: Label -> Label -> Loop -> Loop
setFinalGoto from to = updateBlock from 
                                   (setBlockFinal $ gotoStmt to)


-- | Add an empty block to the loop. Does nothing if the block exists
touchBlock :: Label -> Loop -> Loop
touchBlock label loop = updateBlock label id {-do nothing-} loop



--------------------------------------------------------------------------------
-- * Working with synonym labels


-- | Add synonym labels for the basic predefined labels (init, guard, etc..)
addDefaultSynonymLabels :: Id -> Id -> Loop -> Loop
addDefaultSynonymLabels = addSynonymLabels stdLabelNames


-- | Add synonym labels for a given list of labels.
addSynonymLabels :: [Name] -> Id -> Id -> Loop -> Loop
addSynonymLabels labels nu old loop = foldl alias loop labels
  where
    alias loop lblName = addSynonymLabel (Label lblName nu) (Label lblName old) loop


addSynonymLabel :: Label -> Label -> Loop -> Loop
addSynonymLabel nu old loop
  = loop { loopBlockMap = AMap.addSynonym nu old (loopBlockMap loop) }


-------------------------------------------------------------------------------
-- * Loop statement management

-- | Append a statement to the specified code block.
addStmt :: Stmt -> Label -> Loop -> Loop
addStmt stmt lbl = updateBlock lbl (addStmtsToBlock [stmt])


-- | Append multiple statements to the specified code block.
addStmts :: [Stmt] -> Label -> Loop -> Loop
addStmts stmts lbl = updateBlock lbl (addStmtsToBlock stmts)


-- | Replace all statements (excluding final) in a block with the specified ones.
replaceStmts :: [Stmt] -> Label -> Loop -> Loop
replaceStmts stmts lbl = updateBlock lbl (setStmtsOfBlock stmts)


-- | Moves the statement defining a variable and all of its dependencies
--   to a different block
moveWithDeps :: Var -> Label -> Label -> Loop -> Loop
moveWithDeps v src dst loop = addStmts deps dst
                            $ replaceStmts notDeps src
                            $ loop
  where
    -- All statements of the source block
    stmts = blockBodyStmts $ getBlock src loop

    -- Those statements that are deps of v and those that aren't
    (deps,notDeps) = extractWithDeps v stmts


-------------------------------------------------------------------------------
-- * Other loop functions

setLoopEntry :: Label -> Loop -> Loop
setLoopEntry lbl loop = loop { loopEntry = Just lbl }


unsafeLoopEntry :: Loop -> Label
unsafeLoopEntry = fromMaybe noEntryErr . loopEntry
  where
    noEntryErr = error "exendedEnv: loop entry must be specified"


addToSkipIncrs :: Unique -> Loop -> Loop
addToSkipIncrs uq loop = loop { loopSkipIncrs = uq : loopSkipIncrs loop }


addToSkipTests :: Unique -> Loop -> Loop
addToSkipTests uq loop = loop { loopSkipTests = uq : loopSkipTests loop }


addArg :: Var -> Arg -> Loop -> Loop
addArg var arg loop = loop { loopArgs = loopArgs' }
  where loopArgs' = Map.insert var arg (loopArgs loop)



-------------------------------------------------------------------------------
-- * Rates management

setTheRate :: Unique -> Loop -> Loop
setTheRate uq loop = loop { loopTheRate = Just uq }


getJustRate :: Loop -> Unique
getJustRate loop = fromMaybe err (loopTheRate loop)
  where
    err = error 
        $ "getJustRate: This loop does not have the rate set." ++\ pprLoop loop


-- | Sets the index of the *previous* combinator in a pipeline to be the same
--   as the index of the current combinator, effectively making the rates equal.
--
-- Rate changing combinators like @filter@ should use @newRate@ function.
reuseRate :: Unique -> Unique -> Loop -> Loop
reuseRate new old loop = loop { loopRates = unionInsert new old (loopRates loop) }


freshRate :: Unique -> Loop -> Loop
freshRate rate loop = loop { loopRates = Rates.insert rate (loopRates loop) }


-- | Sets @(segd_rate, data_rate)@ of a @loop@.
setNesting :: (Unique, Unique) -> Loop -> Loop
setNesting rates loop = loop { loopNest = Just rates }


getNesting :: Loop -> Maybe (Unique, Unique)
getNesting = loopNest



-------------------------------------------------------------------------------
-- * Scalar and Array results manipulation

setArrResultImpl :: Maybe Id -> Loop -> Loop
setArrResultImpl mbId loop = loop { loopArrResult = mbId }


setArrResult :: Id -> Loop -> Loop
setArrResult i = setArrResultImpl (Just i)


unsetArrResult :: Loop -> Loop
unsetArrResult = setArrResultImpl Nothing


setScalarResultImpl :: Maybe Var -> Loop -> Loop
setScalarResultImpl mbVar loop = loop { loopScalarResult = mbVar }


setScalarResult :: Var -> Loop -> Loop
setScalarResult v = setScalarResultImpl (Just v)


unsetScalarResult :: Loop -> Loop
unsetScalarResult = setScalarResultImpl Nothing


-- | Unsets scalar result along the way.
setArrResultOnly :: Id -> Loop -> Loop
setArrResultOnly i = unsetScalarResult
                   . setArrResult i



-------------------------------------------------------------------------------
-- * LiveFusion-specific loop functions


-- | A loop with the default set of basic blocks and control flow.
defaultLoop :: Id -> Loop
defaultLoop uq = setTheRate uq
               $ freshRate uq
               $ addDefaultControlFlow uq
               $ setLoopEntry (initLbl uq)
               $ touchDefaultBlocks uq
               $ emptyLoop


-- | Add control flow between some of the known blocks
addDefaultControlFlow :: Id -> Loop -> Loop
addDefaultControlFlow uq loop
  = foldl addFinalGoto loop
  $ [ (initLbl   , guardLbl)  -- Init   -> Guard
    , (guardLbl  , nestLbl)   -- Guard  -> Nest
    , (nestLbl   , bodyLbl)   -- Nest   -> Body
    , (bodyLbl   , yieldLbl)  -- Body   -> Yield
    , (yieldLbl  , bottomLbl) -- Yield  -> Bottom
    , (bottomLbl , guardLbl)  -- Bottom -> Guard
    ]
  where
    addFinalGoto loop (from,to)
      = let fromLbl = from uq
            toLbl = to uq
        in  updateBlock fromLbl
                        (setBlockFinal $ gotoStmt toLbl)
                        loop


-- | Make sure all default blocks exist before we start adding synonyms.
--
--   This would usually happen in fresh loop. But for now we do it in pure
--   generators and nested combinators.
--
--   TODO: should probably not be necessary
touchDefaultBlocks :: Id -> Loop -> Loop
touchDefaultBlocks uq loop = foldl (flip touchBlock) loop stdLabels
  where
    stdLabels = mkLabels stdLabelNames uq
