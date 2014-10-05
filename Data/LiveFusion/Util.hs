{-# LANGUAGE ScopedTypeVariables #-}
module Data.LiveFusion.Util where

import Data.List
import Text.Printf
import Debug.Trace

dEBUG :: Bool
dEBUG = False


log :: String -> a -> a
log str a | dEBUG == True = trace str a
          | otherwise     = a


-- | Concatenate two strings with newline.
infixr 5  ++\
(++\) :: String -> String -> String
(++\) l r = l ++ "\n" ++ r


-- | Concatenate two strings with semicolon and newline.
infixr 5  ++:\
(++:\) :: String -> String -> String
(++:\) str1 str2 = str1 ++ ";\n" ++ str2

-- | Juxtapose two strings.
infixr 5  +-+
(+-+) :: String -> String -> String
(+-+) = space


-- | Juxtapose two strings.
space :: String -> String -> String
space str1 str2 = str1 ++ " " ++ str2


-- | Parenthesise two string.
paren :: String -> String
paren s = "(" ++ s ++ ")"


-- | Indent each line the specified number of steps (2 spaces each).
indent :: Int -> String -> String
indent n = unlines . map (replicate (n*2) ' ' ++) . lines


-- | Neatly index multiple lines.
indexed :: String -> String
indexed = unlines . indexed' . lines
  where
    indexed' :: [String] -> [String]
    indexed' = zipWith space
                       (map linum [2..])  -- GHC errors are off by 1 line
    linum (i::Int) = printf "%2d" i


showStringList :: [String] -> String
showStringList = brackets . intercalate ", "
  where brackets s = "[" ++ s ++ "]"


intercalateMap :: String -> (a -> String) -> [a] -> String
intercalateMap sep f = intercalate sep . map f


juxtMap :: (a -> String) -> [a] -> String
juxtMap f = intercalateMap " " f


-- | Like break but will also take the first matching element.
breakIncl :: (a -> Bool) -> [a] -> ([a],[a])
breakIncl p (x:xs)
  | p x        = ([x],xs)
  | otherwise  = let (ls,rs) = breakIncl p xs
                 in  (x:ls,rs)
breakIncl _ [] = ([],[])


-- | partition2 (==3) [1,4,3,2,3,3,1] = [[1,4,3],[2,3],[3],[1]]
partition2 :: (a -> Bool) -> [a] -> [[a]]
partition2 _ [] = []
partition2 p xs
  = let (ls, rs) = breakIncl p xs
    in  ls : partition2 p rs


-- | Borrowed from Language.Haskell.TH.Syntax
thenCmp :: Ordering -> Ordering -> Ordering
thenCmp EQ o2 = o2
thenCmp o1 _  = o1


-- | Pick ordering from a fixed order given by a list.
--
-- If the value is not in the list it's bigger.
fixedCompare :: Ord a => [a] -> a -> a -> Ordering
fixedCompare order x y = cmp mbx mby
  where
    cmp (Just xi) (Just yi) = compare xi yi
    cmp _         Nothing   = LT
    cmp Nothing   _         = GT
    mbx = elemIndex x order
    mby = elemIndex y order


-- | Sort list on keys.
sortOnKeysBy :: Ord k => (k -> k -> Ordering) -> [(k,v)] -> [(k,v)]
sortOnKeysBy cmp = sortBy (\a b -> (fst a) `cmp` (fst b))


-- | Trace show a value
tr :: Show a => a -> a
tr a = trace (show a) a
