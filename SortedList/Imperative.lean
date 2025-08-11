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

/-- Every element in the input is in the output -/
theorem unique_spec_supset (l : List Int) : l ⊆ unique l := by
  generalize h : unique l = r
  apply Id.by_wp h _
  mvcgen
  case inv =>
    exact ⇓⟨⟨c, out⟩, xs⟩ =>
        (∀ x, some x = c → x ∈ out) ∧ -- c is always in out
        xs.pref ⊆ out -- property holds for out

  all_goals simp_all
  case post.success =>
    intros
    assumption

abbrev StrictSorted (xs : List Int) := Pairwise (· < ·) xs

/-- Main lemma: Given a sorted list as input, `unique` returns a strictly sorted list. -/
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

theorem StrictSorted.sorted (h : StrictSorted xs) : Sorted xs := by grind

-- Adversarially defining `unique` to be the identity function already satisfies the superset property and order preservation, however the correct implementation returns a strictly increasing list, which means there are no duplicate elements.
theorem StrictSorted.nodup (h : StrictSorted xs) : Nodup xs := by grind

theorem StrictSorted.iff : StrictSorted xs ↔ Sorted xs ∧ Nodup xs := by grind

/-- An example for composing above results -/
theorem unique_spec_nodup (l : List Int) (hl : Sorted l) : Nodup (unique l) := by
  apply StrictSorted.nodup
  exact unique_spec_strictSorted l hl

/-- The key property that `unique` must have: Every element in the input is in the output and the output is strictly increasing (or equivalently, doesn't contain duplicates and is sorted). -/
theorem unique_spec (l : List Int) (hl : Sorted l) : let r := unique l; l ⊆ r ∧ StrictSorted r := by
  constructor
  · exact unique_spec_supset l
  · exact unique_spec_strictSorted l hl
