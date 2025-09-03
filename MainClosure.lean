import Std.Tactic.Do

open Std Do List

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
end List

abbrev SortedList := { l : List Int // l.Sorted }

/-- For a sorted list of integers, returns a sorted list of its unique elements.

This is the "refined" version of the `unique` function.
-/
def SortedList.unique (l : SortedList) : SortedList := ⟨_root_.unique l.val, unique_spec.sorted_if_sorted _ l.property⟩

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
