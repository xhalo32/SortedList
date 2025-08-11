-- SortedList.hs:
-- The most important piece to hide is the SortedList constructor
module SortedList (unique', SortedList (), nil, cons, toList, unique, fromList) where

import Data.List

unique' :: [Int] -> [Int]
unique' [] = []
unique' (x : xs) = x : unique' (dropWhile (== x) xs)

newtype SortedList
  = -- The "unsafe" constructor, must not be accessible directly by downstream code
    SortedList [Int]
  deriving (Show, Eq)

nil :: SortedList
nil = SortedList []

cons :: Int -> SortedList -> SortedList
cons x (SortedList l) = SortedList (insert x l)

toList :: SortedList -> [Int]
toList (SortedList l) = l

unique :: SortedList -> [Int]
unique (SortedList l) = unique' l

fromList :: [Int] -> SortedList
fromList = SortedList . sort
