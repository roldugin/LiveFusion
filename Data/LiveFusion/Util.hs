{-# LANGUAGE ScopedTypeVariables #-}
module Data.LiveFusion.Util where

import Data.List
import Text.Printf

-- | Concatenate two strings with newline
infixr 5  ++\
(++\) :: String -> String -> String
(++\) l r = l ++ "\n" ++ r


-- | Concatenate two strings with semicolon and newline
infixr 5  ++:\
(++:\) :: String -> String -> String
(++:\) str1 str2 = str1 ++ ";\n" ++ str2


-- | Juxtapose two strings.
space :: String -> String -> String
space str1 str2 = str1 ++ " " ++ str2


-- | Parenthesise two string.
paren :: String -> String
paren s = "(" ++ s ++ ")"


-- | Indent each line the specified number of steps (2 spaces each)
indent :: Int -> String -> String
indent n = unlines . map (replicate (n*2) ' ' ++) . lines


-- | Neatly index multiple lines
indexed :: String -> String
indexed = unlines . indexed' . lines
  where
    indexed' :: [String] -> [String]
    indexed' = zipWith space
                         (map linum [1..])
    linum (i::Int) = printf "%2d" i


showStringList :: [String] -> String
showStringList = brackets . intercalate ", "
  where brackets s = "[" ++ s ++ "]"


intercalateMap :: String -> (a -> String) -> [a] -> String
intercalateMap sep f = intercalate sep . map f


juxtMap :: (a -> String) -> [a] -> String
juxtMap f = intercalateMap " " f
