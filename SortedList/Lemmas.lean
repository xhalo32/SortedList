import SortedList.Basic

namespace List

theorem Pairwise.cons_of_trans {R : α → α → Prop} (R_trans : ∀ {a b c}, R a b → R b c → R a c) (h : Pairwise R (x :: xs)) (ha : R a x) : Pairwise R (a :: x :: xs) := by
  apply Pairwise.cons _ h
  intro y hy
  simp at h
  cases hy with
  | head =>
    exact ha
  | tail _ hy =>
    obtain ⟨h1, h2⟩ := h
    specialize h1 y hy
    exact R_trans ha h1

theorem Sorted.tail {x : Int} {xs : List Int} (h : Sorted (x :: xs)) : Sorted xs := Pairwise.of_cons h

theorem Sorted.cons (h : Sorted (x :: xs)) (ha : a ≤ x) : Sorted (a :: x :: xs) := Pairwise.cons_of_trans Int.le_trans h ha

theorem Sorted.head_tail (h : Sorted (x :: y :: xs)) : Sorted (x :: xs) := by
  simp at h
  obtain ⟨⟨hxy, h1⟩, h2, h3⟩ := h
  constructor
  · intro a ha
    exact h1 _ ha
  · exact h3

theorem Sorted.cons_tail (h : Sorted (x :: xs)) (hy : y ≤ x) : Sorted (y :: xs) := by
  cases xs with
  | nil =>
    simp
  | cons z xs =>
    apply Sorted.cons (h.tail)
    simp at h
    exact Int.le_trans hy h.1.1

theorem Sorted.dropWhile_eq {x : Int} {xs : List Int} (h : Sorted (x :: xs)) : Sorted (xs.dropWhile (· == x)) := by
  -- induction is the same as match
  induction xs with
  | nil =>
    exact Pairwise.nil
  | cons y xs tail_ih =>
    simp only [dropWhile_cons, beq_iff_eq]
    split
    · subst y
      apply tail_ih
      exact Sorted.tail h
    · exact Sorted.tail h

/-- The size of `dropWhile f xs` is at most the size of `xs`.

Useful for general recursion / induction with a custom proof of termination.
-/
theorem dropWhile_sizeOf_le {xs : List Int} : sizeOf (xs.dropWhile f) ≤ sizeOf xs := by
  induction xs with
  | nil =>
    simp only [dropWhile_nil, nil.sizeOf_spec]
    exact Nat.le_refl _
  | cons y xs tail_ih =>
    simp only [dropWhile_cons, beq_iff_eq]
    split
    · apply Nat.le_trans tail_ih
      simp only [cons.sizeOf_spec]
      exact Nat.le_add_left _ _
    · exact Nat.le_refl _

theorem dropWhile_eq_sizeOf_le {x : Int} {xs : List Int} : sizeOf (xs.dropWhile (· == x)) ≤ sizeOf xs := dropWhile_sizeOf_le

/- Negative results about sortedness -/

theorem Sorted.not_cons_of_not_sorted (h : ¬Sorted (y :: xs)) : ¬ Sorted (x :: y :: xs) := h ∘ Sorted.tail

theorem Sorted.not_cons_of_not_le (h : ¬ x ≤ y) : ¬ Sorted (x :: y :: xs) := by
  intro (Pairwise.cons h1 h2)
  simp at h1
  exact h h1.1

/- Results about membership -/

/-- An element in a list is in the tail part with all values of `y` dropped from the front. -/
theorem mem_dropWhile_of_mem_ne {a y : Int}
  (ha : a ∈ xs) (heq : a ≠ y) : a ∈ dropWhile (· == y) xs :=
by
  induction xs with
  | nil => simp at ha
  | cons hd tl ih =>
    simp only [dropWhile]
    by_cases h : hd = y
    case pos =>
      simp [h]
      apply ih
      cases ha with
      | head =>
        contradiction
      | tail _ ha =>
        simp at h
        exact ha
    case neg =>
      simp [beq_eq_false_iff_ne.mpr h]
      cases ha with
      | head =>
        simp
      | tail _ ha =>
        right
        assumption

/-- `List.mergeSort` returns a `Sorted` list -/
theorem Sorted.mergeSort (l : List Int) : Sorted (l.mergeSort) := by
  have := sorted_mergeSort (le := fun (x y : Int) => decide (x ≤ y))
  simp_all
  exact this @Int.le_trans @Int.le_total _


theorem append_sorted_of_forall_le (hxs : xs.Sorted) (hys : (y :: ys).Sorted) (h : ∀ (a : Int), a ∈ xs → a ≤ y) : (xs ++ (y :: ys)).Sorted := by
  rw [Sorted]
  rw [pairwise_append]
  simp_all
  grind
