module Data.LiveFusion.FuzzyMap where

import Data.Set ( Set, (\\) )
import qualified Data.Set as Set

import Data.Vector ( Vector, (!?), (//) )
import qualified Data.Vector as V

import Data.Maybe
import Control.Arrow ( first )
import Data.Functor
import Prelude hiding ( lookup )


type FuzzyStor k a = Vector (Set k, a)

data FuzzyMap k a = FuzzyMap (FuzzyStor k a)
			

-- | Insert a new key and value in the map. If the key is already present in
--   the map, the associated value is replaced with the supplied value.
insert :: Ord k => k -> a -> FuzzyMap k a -> FuzzyMap k a
insert k v = modifyStor insert'
  where
    insert' stor = case lookupIndex stor k of
                     Just i  -> adjustExisting i stor
                     Nothing -> insertNew stor
    adjustExisting i = adjust i (addKey k)
    insertNew stor   = stor `V.snoc` (Set.singleton k, v)
    addKey k (ks,v)  = (Set.insert k ks, v)


member :: Ord k => k -> FuzzyMap k a -> Bool
member k m = isJust $ lookup k m


notMember :: Ord k => k -> FuzzyMap k a -> Bool
notMember = (not .) . member


-- | The first argument is the 'new' synonym for an existing 'old' key provided
--   in the second argument.
-- 
--   1. If the 'new' key is already in the map, it's removed first then inserted as
--      synonym to the 'old' key appropriately.
--
--   2. If the 'old' key is not in the map the 'new' key is ignored.
--      Be careful, the 'new' key will be removed from the map in this case.
--
-- Implementation warning: The above rules are followed to author's best knowledge.
-- However, one must be careful dealing with the case where 'new == old' and not to
-- remove the 'new' key prematurely.
addSynonym :: Ord k => k -> k -> FuzzyMap k a -> FuzzyMap k a
addSynonym new old = modifyStor (V.map (first adjustKeys))
  where
    adjustKeys keys
      = if   Set.member old keys
        then Set.insert new keys
        else Set.delete new keys



(!) :: Ord k => FuzzyMap k a -> k -> a
(!) m k = fromMaybe (error "Error: element not in the FuzzyMap")
                    (lookup k m)


lookup :: Ord k => k -> FuzzyMap k a -> Maybe a
lookup k m = snd <$> V.find isAmongKeys (stor m)
  where isAmongKeys = (k `Set.member`) . fst


empty :: FuzzyMap k a
empty = FuzzyMap V.empty


elems :: FuzzyMap k a -> [a]
elems = V.toList . V.map snd . stor


-- | /O(n)/. Return all keys of the map in ascending order.
keys :: FuzzyMap k a -> [Set k]
keys = V.toList . V.map fst . stor


-- | /O(n). An alias for toAscList. Return all key/value pairs in the map in
--   ascending key order.
assocs :: FuzzyMap k a -> [(Set k, a)]
assocs = V.toList . stor


-------------------------------------------------------------------------------
-- Stor manipulation

modifyStor :: Ord k => (FuzzyStor k a -> FuzzyStor k a) -> FuzzyMap k a -> FuzzyMap k a
modifyStor f (FuzzyMap stor) = FuzzyMap (f stor)


stor :: FuzzyMap k a -> FuzzyStor k a
stor (FuzzyMap stor) = stor


lookupIndex :: Ord k => FuzzyStor k a -> k -> Maybe Int
lookupIndex stor k = V.findIndex isAmongKeys stor
  where isAmongKeys = (k `Set.member`) . fst


-------------------------------------------------------------------------------
-- Vector helper functions


adjust :: Int -> (a -> a) -> Vector a -> Vector a
adjust i f v = write v i new
  where new = f old
        old = v V.! i


write :: Vector a -> Int -> a -> Vector a
write v i x = v // [(i,x)]
