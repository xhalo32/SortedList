import Std.Tactic.Do

open Std Do

set_option mvcgen.warning false

def reverse (xs : List α) : Id (List α) := do
  let mut out := []

  for x in xs do
    out := x :: out

  return out

#eval reverse [1, 2, 3, 4, 5]

-- Property of being reversed: the length is the same
theorem reverse_spec_length (l : List α) :
    ⦃⌜True⌝⦄ reverse l ⦃⇓r => ⌜r.length = l.length⌝⦄ := by
  mvcgen [reverse]
  case inv1 =>
    -- Loop invariant: `out` has the same number of elements as were in the prefix before the loop
    exact ⇓⟨xs, out⟩ => ⌜ xs.prefix.length = out.length ⌝

  all_goals simp_all <;> grind

-- Property of being reversed: the index of each element is reversed
theorem reverse_spec (l : List α) :
    ⦃⌜True⌝⦄ reverse l ⦃⇓r => ⌜∀ i : Fin (l.length), r[i]? = l[l.length - 1 - i]⌝⦄ := by
  mvcgen [reverse]
  case inv1 =>
    -- Loop invariant: `out` has the same number of elements as were in the prefix before the loop
    exact ⇓⟨xs, out⟩ => ⌜ xs.prefix.length = out.length ∧
      ∀ n : Fin (xs.prefix.length), out[n]? = xs.prefix.reverse[n] -- "induction hypothesis": the processed list has the desired property. Note: xs.rpref can be used instead of pref.reverse
      ⌝

  all_goals simp_all

  case pre => grind
  case step =>
    simp_all [List.getElem?_eq_some_iff]
    expose_names
    subst out out_1
    simp_all

    intro n
    obtain ⟨n, hn⟩ := n
    obtain ⟨h1, h2⟩ := h
    simp

    simp [Nat.lt_succ_iff_lt_or_eq] at hn
    rcases hn with hn | hn
    ·
      simp [List.getElem_cons]
      split
      grind
      obtain ⟨h21, h22⟩ := h_1.2 ⟨n - 1, by grind⟩
      simp_all
      rw [show n = n - 1 + 1 by grind]
      simp_all
    ·
      simp [List.getElem_cons]
      split
      grind
      obtain ⟨h21, h22⟩ := h_1.2 ⟨n - 1, by grind⟩
      simp_all
