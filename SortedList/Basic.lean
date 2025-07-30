namespace List

/-- Define `Sorted` -/
abbrev Sorted (l : List Int) := Pairwise (· ≤ ·) l
