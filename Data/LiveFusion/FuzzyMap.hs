module Data.LiveFusion.FuzzyMap where

import Control.Arrow ( first, second )
import Data.Functor
import Data.List as L hiding ( lookup )
import Data.Maybe
import Data.Set ( Set, (\\) )
import qualified Data.Set as Set

import Prelude as P hiding ( lookup )


type FuzzyStor k a = [(Set k, a)]

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
    insertNew stor   = (Set.singleton k, v) : stor
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
addSynonym new old = modifyStor (L.map (first adjustKeys))
  where
    adjustKeys keys
      = if   Set.member old keys
        then Set.insert new keys
        else Set.delete new keys



(!) :: Ord k => FuzzyMap k a -> k -> a
(!) m k = fromMaybe (error "Error: element not in the FuzzyMap")
                    (lookup k m)


lookup :: Ord k => k -> FuzzyMap k a -> Maybe a
lookup k m = snd <$> lookup' k m


lookup' :: Ord k => k -> FuzzyMap k a -> Maybe (Set k, a)
lookup' k m = L.find containKey (stor m)
  where containKey = (k `Set.member`) . fst


lookupAny :: Ord k => Set k -> FuzzyMap k a -> Maybe a
lookupAny ks m = snd <$> lookupAny' ks m


lookupAny' :: Ord k => Set k -> FuzzyMap k a -> Maybe (Set k, a)
lookupAny' ks m = L.find containKeys (stor m)
  where containKeys = intersects ks . fst


empty :: FuzzyMap k a
empty = FuzzyMap []


elems :: FuzzyMap k a -> [a]
elems = L.map snd . stor


-- | /O(n)/. Return all keys of the map in ascending order.
keys :: FuzzyMap k a -> [Set k]
keys = L.map fst . stor


-- | /O(n)/. An alias for toAscList. Return all key/value pairs in the map in
--   ascending key order.
assocs :: FuzzyMap k a -> [(Set k, a)]
assocs = stor


-- | /O(n)/. Map a function over all values in the map.
map :: (a -> b) -> FuzzyMap k a -> FuzzyMap k b
map f = modifyStor mapVals
  where mapVals = L.map (second f)


-- | Unions are tricky in the general case because the the key sets are allowed
--   to overlap arbitrarity. E.g consider:
-- 
-- > union (fromList [([1,2],"a"), ([3,4],"b")]) (fromList [([1,3],"a"), ([4],"b")])
-- 
--   The second entry in the first map has keys contained in both entries of
--   the second map. In this case we assume that the provided maps will not have these
--   properties and simply union with the first entry containing the given key.
--
--   Note that such a stategy may produce an ill formed loop with duplicate keys
--   as in the above example:
-- > ... = fromList [([1,2,3],"a"), ([3,4],"b")] -- BAD!!
union :: Ord k => FuzzyMap k a -> FuzzyMap k a -> FuzzyMap k a
union = unionWith const


unionWith :: Ord k => (a -> a -> a)
          -> FuzzyMap k a
          -> FuzzyMap k a
          -> FuzzyMap k a
unionWith f = unionWithKeys (\_ x y -> f x y)


unionWithKeys :: Ord k => (Set k -> a -> a -> a)
              -> FuzzyMap k a
              -> FuzzyMap k a
              -> FuzzyMap k a
unionWithKeys f = mergeWithKeys (\ks x y -> Just $ f ks x y) id id


mergeWithKeys :: Ord k => (Set k -> a -> b -> Maybe c)
              -> (FuzzyMap k a -> FuzzyMap k c)
              -> (FuzzyMap k b -> FuzzyMap k c)
              -> FuzzyMap k a
              -> FuzzyMap k b
              -> FuzzyMap k c
mergeWithKeys f = mergeWithKeys2 f'
  where
    f' :: Ord k => Set k -> a -> Set k -> b -> Maybe (Set k, c)
    f' ks1 v1 ks2 v2 = snd <$> f (ks1 `Set.union` ks2) v1 v2


mergeWithKeys2 :: Ord k => (Set k -> a -> Set k -> b -> Maybe (Set k,c))
             -> (FuzzyMap k a -> FuzzyMap k c)
             -> (FuzzyMap k b -> FuzzyMap k c)
             -> FuzzyMap k a
             -> FuzzyMap k b
             -> FuzzyMap k c
mergeWithKeys2 f f1 f2 m1 m2 = FuzzyMap $ go (stor m1) (stor m2)
  where
    go :: Ord k => FuzzyStor k a -> FuzzyStor k b -> FuzzyStor k c
    go st1 [] = f1 st1
    go [] st2 = f2 st2
    go st1 st2
      = let (only1, both) = process st1 st2
            (only2, _)    = process st2 st1
        in  (f1 only1) ++ both ++ (f2 only2)
    
    process (kv1@(ks1,v1):st1) st2
      = let (only, both) = process st1 st2
        in  case lookupAny' ks1 st2 of
              Just (ks2,v2) -> let kv = maybeToList $ f ks1 v1 ks2 v2
                               in  (only, kv ++ both)
              Nothing       -> (kv1:only, both)


intersects :: Set a -> Set a -> Bool
intersects s1 s2 = not null $ Set.intersection s1 s2


-- Stor manipulation
-------------------------------------------------------------------------------

modifyStor :: (FuzzyStor k a -> FuzzyStor k b) -> FuzzyMap k a -> FuzzyMap k b
modifyStor f (FuzzyMap stor) = FuzzyMap (f stor)


stor :: FuzzyMap k a -> FuzzyStor k a
stor (FuzzyMap stor) = stor


lookupIndex :: Ord k => FuzzyStor k a -> k -> Maybe Int
lookupIndex stor k = L.findIndex isAmongKeys stor
  where isAmongKeys = (k `Set.member`) . fst


-- List helper functions
-------------------------------------------------------------------------------

adjust :: Int -> (a -> a) -> [a] -> [a]
adjust i f xs = before ++ (f x) : after
  where 
    (before, (x:after)) = splitAt i xs
