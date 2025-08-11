import SortedList (cons, nil, fromList, unique)

main :: IO ()
main = do
  -- The sorted list [1, 1, 2, 2]
  let l = cons 1 $ cons 2 $ cons 1 $ cons 2 nil
  print l
  print $ "Unique elements " ++ show (unique l)

  let l = [4, 5, 2, 4, 2]
  let s = fromList l
  print s
  print $ "Unique elements " ++ show (unique s)
