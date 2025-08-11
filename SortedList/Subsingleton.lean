-- Instead of `Prop` we can technically use `Type` in lean because `Prop` is a universe of subsingletons: types which have at most one element.
-- In these universes all elements (proofs) of the same type (proposition) are definitionally equal.
-- Lean is not meant to be used this way but it is possible.

def Sorted (xs : List Int) : Type :=
  if xs.Pairwise (· ≤ ·)
  then Unit
  else Empty

noncomputable
def Sorted.cons (h : Sorted xs) (hx : ∀ a ∈ xs, x ≤ a) : Sorted (x :: xs) := by
  unfold Sorted at *
  split at h
  next h1 =>
    split
    · exact h
    next h2 =>
      simp at h2
      simp_all
  next h1 =>
    nomatch h
