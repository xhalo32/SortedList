import SortedList.SortedList

open IO

def main : IO Unit := do
  let stdin ← IO.getStdin
  while true do
    -- Read a list of integers from the stdin
    let line ← stdin.getLine
    let list := Int.ofNat <$> String.toNat! <$> (line |>.stripSuffix "\n" |>.split (· == ' '))
    println s!"Your input: {repr list}"

    -- Use the fact that Sorted is decidable
    if h : list.Sorted then
      -- In this branch `h` is a proof of `list.Sorted`.
      let unique_elems := list.unique h
      println s!"Unique elements: {unique_elems}"

    else
      -- And here `h` is a proof of `¬ list.Sorted`.
      let idx := List.Sorted.not_sorted_idx h
      println s!"Input was not sorted at index {idx}"

      -- Sort the list
      let sorted_list := list.sort
      println s!"Your input (sorted): {sorted_list.1}"

      -- Get the unique elements
      let unique_elems := sorted_list.unique
      println s!"Unique elements: {unique_elems}"
