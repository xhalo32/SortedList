import Std.Tactic.Do

open Std Do List

set_option mvcgen.warning false

/-- Given a list, returns the list of its unique elements **assuming** the list is in order.

Use `SortedList` API instead: `SortedList.unique : SortedList → SortedList`.
-/
private def unique (xs : List Int) : List Int := Id.run do
  let mut c : Option Int := none -- previous x in the list
  let mut out := [] -- output of the function

  for x in xs do
    if some x != c then
      out := out ++ [x]
      c := some x

  out


namespace List

/-- A list is `Sorted` when it is pairwise in a ≤-relation.

For example `Sorted [1, 2, 3]` is equivalent with `(1 ≤ 2 ∧ 1 ≤ 3) ∧ 2 ≤ 3`.
Here `2 ≤ 3` comes from the requirement that the tail is sorted: `Sorted [2, 3] ↔ 2 ≤ 3`.
-/
abbrev Sorted (l : List Int) := Pairwise (· ≤ ·) l

abbrev StrictSorted (l : List Int) := Pairwise (· < ·) l

theorem StrictSorted.sorted (h : StrictSorted l) : Sorted l := by
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

end List

abbrev SortedList := { l : List Int // l.Sorted }

/-- For a sorted list of integers, returns a sorted list of its unique elements.

This is the "refined" version of the `unique` function.
-/
def SortedList.unique (l : SortedList) : SortedList := ⟨_root_.unique l.val, (unique_spec_strictSorted _ l.property).sorted⟩

/-- `List.mergeSort` returns a `Sorted` list -/
theorem Sorted.mergeSort (l : List Int) : Sorted (l.mergeSort) := by
  have := sorted_mergeSort (le := fun (x y : Int) => decide (x ≤ y))
  simp_all
  exact this @Int.le_trans @Int.le_total _

namespace List

def sort (l : List Int) : SortedList := ⟨l.mergeSort, Sorted.mergeSort l⟩

-- Now a couple of lemmas about `Sorted`.

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

theorem Sorted.cons (h : Sorted (x :: xs)) (ha : a ≤ x) : Sorted (a :: x :: xs) := Pairwise.cons_of_trans Int.le_trans h ha

theorem Sorted.not_tail_of_le (h : ¬(x :: y :: xs).Sorted) (hxy : x ≤ y) : ¬ (y :: xs).Sorted := by
  false_or_by_contra
  apply h
  exact cons ‹_› ‹_›

def Sorted.not_sorted_idx (h : ¬ Sorted xs) : Nat := match xs with
  | [] => nomatch h
  | [_x] => by
    simp at h
  | (x :: y :: xs) =>
    if hxy : x ≤ y then
      1 + Sorted.not_sorted_idx (Sorted.not_tail_of_le h hxy)
    else
      1

end List

section main

open IO

def main : IO Unit := do
  let stdin ← IO.getStdin
  while true do
    -- Read a list of integers from the stdin
    let line ← stdin.getLine
    let list := Int.ofNat <$> String.toNat! <$> (line |>.stripSuffix "\n" |>.split (· == ' '))
    println s!"Your input: {list}"

    -- Use the fact that Sorted is decidable
    if h : list.Sorted then
      -- In this branch `h` is a proof of `list.Sorted`.
      let unique_elems : SortedList := SortedList.unique ⟨list, h⟩
      println s!"Unique elements: {unique_elems}"

    else
      -- And here `h` is a proof of `¬ list.Sorted`.
      let idx := List.Sorted.not_sorted_idx h
      println s!"Input was not sorted at index {idx}"

      -- Sort the list
      let sorted_list := list.sort
      println s!"Your input (sorted): {sorted_list.val}"

      -- Get the unique elements
      let unique_elems : SortedList := sorted_list.unique
      println s!"Unique elements: {unique_elems}"

def main_live_example : IO Unit := do
  let list := [0, 2, 1, 3, 1, 0]
  println s!"Your input: {list}"

  -- Use the fact that Sorted is decidable
  if h : list.Sorted then
    -- In this branch `h` is a proof of `list.Sorted`.
    let unique_elems : SortedList := SortedList.unique ⟨list, h⟩
    println s!"Unique elements: {unique_elems}"

  else
    -- And here `h` is a proof of `¬ list.Sorted`.
    let idx := List.Sorted.not_sorted_idx h
    println s!"Input was not sorted at index {idx}"

    -- Sort the list
    let sorted_list := list.sort
    println s!"Your input (sorted): {sorted_list.val}"

    -- Get the unique elements
    let unique_elems : SortedList := sorted_list.unique
    println s!"Unique elements: {unique_elems}"

#eval main_live_example
/-
Your input: [0, 2, 1, 3, 1, 0]
Input was not sorted at index 2
Your input (sorted): [0, 0, 1, 1, 2, 3]
Unique elements: [0, 1, 2, 3]
-/
