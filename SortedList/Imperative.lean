-- Tested on Lean 4 v4.23.0-rc2

import Std.Tactic.Do
import SortedList.Specification
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

theorem unique_spec_supset (l : List Int) : l ⊆ unique l := by
  generalize h : unique l = r
  apply Id.of_wp_run_eq h _

  -- Using the monadic verification condition generator, we can split the proof into 4 steps.
  mvcgen

  -- First, we need to provide an invariant that holds before, during, and after the for loop.
  case inv1 =>
    exact ⇓⟨xs, c, out⟩ =>
      ⌜ (∀ x, some x = c → x ∈ out) ∧ -- First invariant: c is always in out
        xs.prefix ⊆ out ⌝ -- Second invariant: main property (`l ⊆ unique l`) holds for out

  -- We can simplify all goals to see the individual steps better
  -- clear c out
  -- obtain ⟨c, out⟩ := b
  all_goals dsimp at *
  -- all_goals simp only [reverse_subset, true_imp_iff] at *

  -- The first two goals state that assuming that the invariant holds before the loop iteration (`h`), the invariant holds after the loop iteration.
  -- There are two goals to analyze both code branches of `if some x != c then ...`
  -- The next goal `pre1` states that the invariant holds before the loop.

  -- Proof automation takes care of the first three goals.
  all_goals simp_all
  case step.isTrue => grind
  case step.isFalse => grind

  -- The last goal states that if the loop condition holds after the loop, the main statement `l ⊆ unique l` holds.
  case post.success =>
    intro inv1 inv2
    simp only [wp, Id.run, PredTrans.pure_apply]
    exact inv2

theorem unique_spec_subset (l : List Int) : unique l ⊆ l := by
  generalize h : unique l = r
  apply Id.of_wp_run_eq h _
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, c, out⟩ =>
      ⌜ (∀ x, some x = c → x ∈ out) ∧ -- c is always in out
        out ⊆ xs.prefix ⌝ -- property holds for out

  all_goals simp_all
  case step.isTrue => grind
  case step.isFalse => grind

  case post.success =>
    intro h1 h2
    exact h2

-- A list is strictly sorted if every element is strictly less than the next
abbrev StrictSorted (xs : List Int) := Pairwise (· < ·) xs

theorem StrictSorted.sorted (h : StrictSorted xs) : Sorted xs := by
  grind [= pairwise_iff_forall_sublist]

theorem StrictSorted.nodup (h : StrictSorted xs) : Nodup xs := by
  grind [= pairwise_iff_forall_sublist]

theorem StrictSorted.iff : StrictSorted xs ↔ Sorted xs ∧ Nodup xs := by
  grind [= pairwise_iff_forall_sublist]

/-- Key lemma: Given a sorted list as input, `unique` returns a strictly sorted list. -/
theorem unique_spec_strictSorted (l : List Int) (hl : Sorted l) : StrictSorted (unique l) := by
  generalize h : unique l = r
  apply Id.of_wp_run_eq h _
  mvcgen
  case inv1 =>
    exact ⇓⟨xs, c, out⟩ =>
      ⌜ (∀ x ∈ out, x ≤ c) ∧ -- out ≤ c
        (∀ x ∈ xs.suffix, c ≤ x) ∧ -- c is always ≤ the rest of the input (i.e. suffix)
        StrictSorted out ⌝ -- property holds for out

  all_goals simp_all
  case step.isTrue h =>
    obtain ⟨hout_le, ⟨hc, hc_le⟩, h_strictSorted⟩ := h
    expose_names
    -- There are still references to b in hout_le, let's clean them away
    subst c out
    rcases b with ⟨c, out⟩
    dsimp at *

    have lemma1 (y) (hy : y ∈ out) : y < cur := by
      rcases c with _ | c
      · specialize hout_le y hy
        contradiction
      · simp_all
        grind

    have hs : (cur :: suff).Sorted := by grind
    simp [Sorted] at hs
    grind
  case step.isFalse => grind
  case post.success =>
    intros
    assumption


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
