import SortedList.Lemmas

namespace List

/-- Decide whether an arbitrary list is Sorted.

This is not only an algorithm for checking if an arbitrary list is sorted,
but also a "proof machine" capable of constructing the proof that it is or isn't!
-/
def Sorted.decide (xs : List Int) : Decidable (Sorted xs) := match xs with
| [] => .isTrue Pairwise.nil
| [_x] => .isTrue (Pairwise.cons (by simp) Pairwise.nil)
| (x :: y :: xs) =>
  if hxy : x ≤ y then
    match Sorted.decide (y :: xs) with
    | Decidable.isTrue h_tail =>
      .isTrue (h_tail.cons hxy)
    | Decidable.isFalse h =>
      .isFalse (not_cons_of_not_sorted h)
  else
    .isFalse (not_cons_of_not_le hxy)

-- The above fact is already proved in the Lean standard library
example (xs : List Int) : Decidable (Sorted xs) := instDecidablePairwise xs

-- Therefore the following instance is redundant
instance {xs : List Int} : Decidable (Sorted xs) := Sorted.decide xs

-- What lean computes here is not merely a boolean, but a complete **proof object**,
-- which contains the mathematical proof that the list is sorted.
#eval Sorted [1, 2, 3, 3]

-- Similarly it computes here a proof that the list is not sorted.
#eval Sorted [1, 2, 3, 2]

theorem Sorted.not_tail_of_le (h : ¬(x :: y :: xs).Sorted) (hxy : x ≤ y) : ¬ (y :: xs).Sorted := by
  false_or_by_contra
  apply h
  exact cons ‹_› ‹_›

/-- Computes the index of the first out of order element.

Requires a proof that the list is not sorted.

For example, for the list `[1, 2, 1]`, the index computed is 2.
-/
def Sorted.not_sorted_idx (h : ¬ Sorted xs) : Nat := match xs with
  | [] => nomatch h
  | [_x] => by
    simp at h
  | (x :: y :: xs) =>
    if hxy : x ≤ y then
      1 + Sorted.not_sorted_idx (Sorted.not_tail_of_le h hxy)
    else
      1


-- `by decide` is used to prove that `¬ Sorted [1, 0]` using decidability.
example : @Sorted.not_sorted_idx [1, 0] (by decide) = 1 := rfl

example : @Sorted.not_sorted_idx [1, 2, 1] (by decide) = 2 := rfl
