import SortedList.Lemmas

/-!
A "functional", i.e. recursive version of the imperative unique function
-/

namespace List

/-- Given a list, returns the list of its unique elements **assuming** the list is in order. -/
def unique' (xs : List Int) : List Int := match xs with
| [] => []
| (x :: xs) =>
  -- Lean requires a proof that recursion terminates by e.g. a decreasing argument.
  -- We know that `xs` is smaller than `(x :: xs)` and also `dropWhile (. == x) xs` is smaller than `xs`.
  have _xs_decreasing := @dropWhile_eq_sizeOf_le x xs
  x :: unique' (dropWhile (. == x) xs)

/-- Given a **sorted** list, returns the list of its unique elements. -/
def unique (xs : List Int) (h : Sorted xs := by decide) : List Int := match xs with
| [] => []
| (x :: xs) =>
  have _xs_decreasing := @dropWhile_eq_sizeOf_le x xs
  x :: unique (dropWhile (. == x) xs) (Sorted.dropWhile_eq h)

/- Properties of unique -/

@[simp] theorem unique_cons : unique (x :: xs) h =
  x :: unique (dropWhile (. == x) xs) (Sorted.dropWhile_eq h) := by
  conv =>
    left
    unfold unique

/-- All elements in a list are also contained in its list of unique elements. -/
theorem unique_complete : ∀ {xs : List Int} (h : Sorted xs), xs ⊆ xs.unique h
  | [], _, _ => by
    simp_all
  | cons x xs, h, a => by
    intro ha
    have _xs_decreasing := @dropWhile_eq_sizeOf_le x xs
    cases ha with
    | head =>
      simp
    | tail _ ha =>
      simp
      by_cases heq : a = x
      · simp_all
      · right
        apply unique_complete
        apply mem_dropWhile_of_mem_ne ha heq
