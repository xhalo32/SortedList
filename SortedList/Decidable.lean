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
