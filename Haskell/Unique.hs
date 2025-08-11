import Data.List

unique :: [Int] -> [Int]
unique [] = []
unique (x : xs) = x : unique (dropWhile (== x) xs)

sorted :: [Int] -> Bool
sorted [] = True
sorted [x] = True
sorted (x : y : xs) = x <= y && sorted (y : xs)

unique' :: [Int] -> Maybe [Int]
unique' [] = Just []
unique' (x : xs)
  | sorted (x : xs) = (x :) <$> unique' (dropWhile (== x) xs)
  | otherwise = Nothing
