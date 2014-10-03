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
  show (Label nm i) = nm ++ "_" ++ show i


class LabelContainer c where
  mapLabels :: (Label -> Label) -> c -> c


pprLabel :: Label -> String
pprLabel = show


-------------------------------------------------------------------------------
-- * Loop specific

--------------------------------------------------------------------------------
-- * Several predefined labels

initNm, guardNm, bodyNm, yieldNm, bottomNm, doneNm :: Name
initNm   = "init"
guardNm  = "guard"
bodyNm   = "body"
yieldNm  = "yield"
bottomNm = "bottom"
doneNm   = "done"


-- | A list of standard label constructors
stdLabelNames :: [Name]
stdLabelNames = [initNm, guardNm, bodyNm, yieldNm, bottomNm, doneNm]


initLbl, guardLbl, bodyLbl, yieldLbl, bottomLbl, doneLbl :: Id -> Label
initLbl   = Label initNm
guardLbl  = Label guardNm
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
theSynonymLabel lbls l = theOneLabel $ synonyms
  where
    synonyms = fromMaybe err
             $ find (l `Set.member`) lbls
    err = error $ "theSynonymLabel: label" +-+ show l +-+ "not found in sets"
