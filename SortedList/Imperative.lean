-- Tested on Lean 4 v4.22-rc4

import Std.Tactic.Do
import SortedList.Lemmas

open Std Do List

set_option mvcgen.warning false

-- Inspiration: <https://markushimmel.de/blog/my-first-verified-imperative-program/>

/-- (Locally) imperative version of the functional `unique` function. -/
def unique (xs : List Int) : List Int := Id.run do
  let mut c : Option Int := none -- previous x in the list
  let mut out := [] -- output of the function

  for x in xs do
    if some x != c then
      out := out ++ [x]
      c := some x

  out

#print unique

#eval unique [1, 1, 2, 2, 3]

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


theorem unique_spec_supset (l : List Int) : l ⊆ unique l := by
  generalize h : unique l = r
  apply Id.by_wp h _
  -- simp only [wp, Id.run, PredTrans.pure_apply]

  -- Using the monadic verification condition generator, we can split the proof into 4 steps.
  mvcgen

  -- First, we need to provide an invariant that holds before, during, and after the for loop.
  case inv =>
    exact ⇓⟨⟨c, out⟩, xs⟩ =>
        (∀ x, some x = c → x ∈ out) ∧ -- First invariant: c is always in out
        xs.pref ⊆ out -- Second invariant: main property (`l ⊆ unique l`) holds for out

  -- We can simplify all goals to see the individual steps better
  -- clear c out
  -- obtain ⟨c, out⟩ := b
  all_goals dsimp at *
  all_goals simp only [reverse_subset, true_imp_iff] at *

  -- The first two goals state that assuming that the invariant holds before the loop iteration (`h`), the invariant holds after the loop iteration.
  -- There are two goals to analyze both code branches of `if some x != c then ...`
  -- The next goal `pre1` states that the invariant holds before the loop.

  -- Proof automation (the simplifier) takes care of the first three goals.
  all_goals simp_all

  -- The last goal states that if the loop condition holds after the loop, the main statement `l ⊆ unique l` holds.
  case post.success =>
    clear c out
    expose_names
    obtain ⟨c, out⟩ := r_1
    dsimp
    intro inv1 inv2
    simp only [wp, Id.run, PredTrans.pure_apply]
    exact inv2

theorem unique_spec_subset (l : List Int) : unique l ⊆ l := by
  generalize h : unique l = r
  apply Id.by_wp h _
  mvcgen
  case inv =>
    exact ⇓⟨⟨c, out⟩, xs⟩ =>
        (∀ x, some x = c → x ∈ out) ∧ -- c is always in out
        out ⊆ xs.pref -- property holds for out

  all_goals simp_all
  case pre1 =>
    rfl
  case post.success =>
    intro h1 h2
    exact h2

-- A list is strictly sorted if every element is strictly less than the next
abbrev StrictSorted (xs : List Int) := Pairwise (· < ·) xs

theorem StrictSorted.sorted (h : StrictSorted xs) : Sorted xs := by grind

theorem StrictSorted.nodup (h : StrictSorted xs) : Nodup xs := by grind

theorem StrictSorted.iff : StrictSorted xs ↔ Sorted xs ∧ Nodup xs := by grind

/-- Key lemma: Given a sorted list as input, `unique` returns a strictly sorted list. -/
theorem unique_spec_strictSorted (l : List Int) (hl : Sorted l) : StrictSorted (unique l) := by
  generalize h : unique l = r
  apply Id.by_wp h _
  mvcgen
  case inv =>
    exact ⇓⟨⟨c, out⟩, xs⟩ =>
        (∀ x ∈ out, x ≤ c) ∧ -- out ≤ c
        (∀ x ∈ xs.suff, c ≤ x) ∧ -- c is always ≤ the rest of the input (i.e. suffix)
        StrictSorted out -- property holds for out

  all_goals simp_all
  case post.success =>
    intros
    assumption

  · obtain ⟨hout_le, ⟨hc, hc_le⟩, h_strictSorted⟩ := h
    generalize b.snd = out at *
    generalize b.fst = c at *

    have lemma1 (y) (hy : y ∈ out) : y < x := by
      rcases c with _ | c
      · specialize hout_le y hy
        contradiction
      · simp_all
        grind

    have hs : (x :: suff).Sorted := by grind
    simp [Sorted] at hs
    grind
  · grind

/-- An example for composing above results -/
theorem unique_nodup (l : List Int) (hl : Sorted l) : Nodup (unique l) := by
  apply StrictSorted.nodup
  exact unique_spec_strictSorted l hl

/-- Main statement: `unique` satisfies the specification. -/
theorem unique_spec : UniqueSpec unique := by
  constructor <;> intro l
  · exact unique_spec_supset l
  · exact unique_spec_subset l
  · intro hl
    apply StrictSorted.sorted
    exact unique_spec_strictSorted l hl
  · intro hl
    apply StrictSorted.nodup
    exact unique_spec_strictSorted l hl
