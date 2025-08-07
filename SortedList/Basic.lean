namespace List

/-- A list is `Sorted` when it is pairwise in a ≤-relation.

For example `Sorted [1, 2, 3]` is equivalent with `(1 ≤ 2 ∧ 1 ≤ 3) ∧ 2 ≤ 3`.
Here `2 ≤ 3` comes from the requirement that the tail is sorted: `Sorted [2, 3] ↔ 2 ≤ 3`.
-/
abbrev Sorted (l : List Int) := Pairwise (· ≤ ·) l

example : Sorted [x, y] ↔ x ≤ y := by simp

example : Sorted [x, y, z] ↔ (x ≤ y ∧ x ≤ z) ∧ y ≤ z := by simp
