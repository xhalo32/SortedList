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

/-- Every element in the input is in the output -/
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
  all_goals dsimp at *; expose_names; try subst c out

  -- The first goal states that the loop invariant holds before the loop
  case pre =>
    constructor
    · intro x hx
      nomatch hx -- `some x = none` is impossible
    · exact nil_subset _

  -- The next goal states that if
  --   1. the loop invariant holds for the previous loop, and
  --   2. we go into the `if`
  -- then the loop invariant holds after the loop.
  case step.isTrue =>
    rcases b with ⟨c, out⟩
    dsimp at *
    constructor
    · intro x hx
      simp at hx
      rw [hx]
      simp
    · simp
      apply subset_append_of_subset_left
      exact h_3.2 -- Second invariant

  -- This goal states that if
  --   1. the loop invariant holds for the previous loop, and
  --   2. we do not go into the `if` (i.e. do nothing in the loop)
  -- then the loop invariant holds after the loop.
  case step.isFalse =>
    rcases b with ⟨c, out⟩
    dsimp at *
    constructor
    · intro x hx
      apply h_3.1 -- First invariant
      exact hx
    · simp
      constructor
      · exact h_3.2 -- Second invariant
      · apply h_3.1 -- First invariant again
        simp at h_2
        exact h_2 -- We did not have `some x != c`, therefore `some x = c`

  -- The last goal states that if the loop invariant holds after the loop, the main statement `l ⊆ unique l` holds.
  case post.success =>
    rcases r_1 with ⟨c, out⟩
    dsimp
    rintro ⟨inv1, inv2⟩
    simp only [wp, Id.run, PredTrans.pure_apply]
    exact inv2
