import SortedList.Basic

open List

/-- The key properties that a `unique` function must have together defines its specification. -/
structure UniqueSpec (unique : List Int → List Int) where
  /-- Every element in the input is in the output -/
  supset : ∀ l, l ⊆ unique l
  /-- Every element in the output is in the input -/
  subset : ∀ l, unique l ⊆ l
  /-- The output is sorted if the input is sorted -/
  sorted_if_sorted : ∀ l, (Sorted l) → Sorted (unique l)
  /-- The output contains no duplicates if the input is sorted -/
  nodup_if_sorted : ∀ l, (Sorted l) → Nodup (unique l)
