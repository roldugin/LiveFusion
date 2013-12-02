module Data.LiveFusion.FuzzyMap where

import Control.Arrow ( first, second )
import Data.Functor
import Data.List as L hiding ( lookup )
import Data.Maybe
import Data.Set ( Set )
import qualified Data.Set as Set

import Prelude as P hiding ( lookup )


type FuzzyStor k a = [(Set k, a)]

type FuzzyMap k a = FuzzyStor k a
			

-- | Insert a new key and value in the map. If the key is already present in
--   the map, the associated value is replaced with the supplied value.
insert :: Ord k => k -> a -> FuzzyMap k a -> FuzzyMap k a
insert k v = modifyStor insert'
  where
    insert' stor = case lookupIndex stor k of
                     Just i  -> adjustExisting i stor
                     Nothing -> insertNew stor
    adjustExisting i = adjust i (replaceVal)
    insertNew stor   = (Set.singleton k, v) : stor
    replaceVal       = second (const v)


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
(!) m k = fromMaybe err (lookup k m)
  where err = error "FuzzyMap.!: element not in the map"


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


-- | /O(n)/. Return all synomyms of a given key.
synonyms :: Ord k => k -> FuzzyMap k a -> Set k
synonyms k m = fst $ fromMaybe err (lookup' k m)
  where err = error "FuzzyMap.synonyms: element not in the map"


empty :: FuzzyMap k a
empty = []


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
    f' ks1 v1 ks2 v2
      = let ks  = ks1 `Set.union` ks2
            mbv = f ks v1 v2
        in  case mbv of
              Nothing -> Nothing
              Just v  -> Just (ks,v)



mergeWithKeys2 :: Ord k => (Set k -> a -> Set k -> b -> Maybe (Set k,c))
             -> (FuzzyMap k a -> FuzzyMap k c)
             -> (FuzzyMap k b -> FuzzyMap k c)
             -> FuzzyMap k a
             -> FuzzyMap k b
             -> FuzzyMap k c
mergeWithKeys2 f f1 f2 m1 m2 = go m1 m2
  where
    go m1 [] = f1 m1
    go [] m2 = f2 m2
    go st1 st2
      = let (only1, both) = process1 m1 m2
            (only2, _)    = process2 m1 m2
        in  (f1 only1) ++ both ++ (f2 only2)
    
    process1 (kv1@(ks1,v1):m1) m2
      = let (only, both) = process1 m1 m2
        in  case lookupAny' ks1 m2 of
              Just (ks2,v2) -> let kv = maybeToList $ f ks1 v1 ks2 v2
                               in  (only, kv ++ both)
              Nothing       -> (kv1:only, both)
    process1 _ _ = ([],[])

    process2 m1 (kv2@(ks2,v2):m2)
      = let (only, both) = process2 m1 m2
        in  case lookupAny' ks2 m1 of
              Just (ks1,v1) -> let kv = maybeToList $ f ks1 v1 ks2 v2
                               in  (only, kv ++ both)
              Nothing       -> (kv2:only, both)
    process2 _ _ = ([],[])


intersects :: Ord a => Set a -> Set a -> Bool
intersects s1 s2 = not $ Set.null $ Set.intersection s1 s2


fromList :: Ord k => [(Set k, a)] -> FuzzyMap k a
fromList = id

fromList1 :: Ord k => [(k,a)] -> FuzzyMap k a
fromList1 = fromListL . L.map (first return)

fromListL :: Ord k => [([k],a)] -> FuzzyMap k a
fromListL = fromList . L.map (first Set.fromList)


-- Stor manipulation (legacy, will be removed)
-------------------------------------------------------------------------------

modifyStor :: (FuzzyStor k a -> FuzzyStor k b) -> FuzzyMap k a -> FuzzyMap k b
modifyStor = id


stor :: FuzzyMap k a -> FuzzyStor k a
stor m = m


lookupIndex :: Ord k => FuzzyStor k a -> k -> Maybe Int
lookupIndex stor k = L.findIndex isAmongKeys stor
  where isAmongKeys = (k `Set.member`) . fst


-- List helper functions
-------------------------------------------------------------------------------

adjust :: Int -> (a -> a) -> [a] -> [a]
adjust i f xs = before ++ (f x) : after
  where 
    (before, (x:after)) = splitAt i xs
