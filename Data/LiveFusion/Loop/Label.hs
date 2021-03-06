module Data.LiveFusion.Loop.Label where

import Data.LiveFusion.Loop.Common

import Data.LiveFusion.Util

import Data.List as List
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Maybe


data Label = Label Name Id
  deriving ( Eq, Ord )


instance Show Label where
  show = pprLabel


class LabelContainer c where
  mapLabels :: (Label -> Label) -> c -> c


pprLabel :: Label -> String
pprLabel (Label nm i) = pprName nm ++ "_" ++ pprId i


-------------------------------------------------------------------------------
-- * Loop specific

--------------------------------------------------------------------------------
-- * Several predefined labels

initNm, guardNm, nestNm, bodyNm, yieldNm, bottomNm, doneNm :: Name
initNm   = "init"
guardNm  = "guard"
nestNm   = "nest"
bodyNm   = "body"
yieldNm  = "yield"
bottomNm = "bottom"
doneNm   = "done"


-- | Labels that are normally shared by loops of all rates
stdSharedNames :: [Name]
stdSharedNames = [initNm, doneNm]


-- | Labels that are shared by loops of "compatible" rates
stdSubrateNames :: [Name]
stdSubrateNames = [guardNm]


-- | Labels that are shared by the the same rate
stdRateNames :: [Name]
stdRateNames = [nestNm, bodyNm, yieldNm, bottomNm]


-- | A list of standard label constructors
stdLabelNames :: [Name]
stdLabelNames = stdSharedNames ++ stdSubrateNames ++ stdRateNames


initLbl, guardLbl, nestLbl, bodyLbl, yieldLbl, bottomLbl, doneLbl :: Id -> Label
initLbl   = Label initNm
guardLbl  = Label guardNm
nestLbl   = Label nestNm
bodyLbl   = Label bodyNm
yieldLbl  = Label yieldNm
bottomLbl = Label bottomNm
doneLbl   = Label doneNm




mkLabels :: [Name] -> Id -> [Label]
mkLabels names uq = map (\nm -> Label nm uq) names


-------------------------------------------------------------------------------
-- * Label sets

-- | Reduces a set of labels to one specific label.
--
--   The reduction function can be anything as long as the loop doesn't change
--   after we start reducing all label synonyms to one concrete label.
theOneLabel :: Set Label -> Label
theOneLabel = Set.findMin 


-- | Rewrites one label to its synonym from the loop following a predefined
--   convention.
theSynonymLabel :: [Set Label] -> Label -> Label
theSynonymLabel lbls l = theOneLabel synonyms
  where
    synonyms = fromMaybe err
             $ find (l `Set.member`) lbls
    err = error $ "theSynonymLabel: label" +-+ pprLabel l +-+ "not found in sets:" ++\ show lbls
