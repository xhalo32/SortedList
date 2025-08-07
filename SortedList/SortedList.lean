import SortedList.Unique

/-
Now let's define List.sort for sorting a list and providing a proof that it is sorted
-/

def SortedList := { l : List Int // l.Sorted }

namespace SortedList
open List

/-- Inserts an element `x` at the first position where `x` is less than the head of the list.

Note: There is already `List.insert` which is not the same.
-/
def insert (x : Int) : List Int → List Int
  | [] => [x]
  | y :: xs =>
    if x ≤ y then
      x :: y :: xs
    else
      y :: insert x xs

@[simp] theorem insert_nil : insert x [] = [x] := rfl

@[simp] theorem insert_cons_le (h : x ≤ y) : insert x (y :: xs) = x :: y :: xs := by
  simp [insert, h]

@[simp] theorem insert_cons_not_le (h : ¬ x ≤ y) : insert x (y :: xs) = y :: insert x xs := by
  simp [insert, h]

theorem head_le_sorted (h : Sorted (x :: xs)) (ha : a ∈ xs) : x ≤ a := by
  induction xs with
  | nil =>
    simp at ha
  | cons y ys ih =>
    cases ha with
    | head =>
      simp at h
      exact h.1.1
    | tail _ ha =>
      exact ih (Sorted.head_tail h) ha

theorem mem_insert_iff : a ∈ insert x xs ↔ a ∈ x :: xs := by
  induction xs with
  | nil =>
    simp
  | cons y ys ih =>
    by_cases hx : x ≤ y
    · simp [hx]
    · simp at ih
      simp [hx]
      rw [ih, or_left_comm]

/-- Insert a new element into a SortedList -/
def cons' (x : Int) (xs : SortedList) : List Int := insert x xs.1

/-- `cons'` preserves sortedness -/
def cons'.sorted (x : Int) (xs : SortedList) : Sorted (cons' x xs) := by
  obtain ⟨l, hl⟩ := xs
  induction l with
  | nil =>
    simp [cons', insert]
  | cons y ys ih =>
    dsimp [cons', insert]
    by_cases h : x ≤ y
    case pos =>
      simp only [h, reduceIte]
      apply Sorted.cons hl h
    case neg =>
      simp [h]
      refine ⟨?_, ih (Sorted.tail hl)⟩
      intro a ha
      rw [mem_insert_iff] at ha
      simp at h
      cases ha with
      | head =>
        exact Int.le_of_lt h
      | tail _ ha =>
        apply head_le_sorted hl ha

/-- Insert a new element into a SortedList -/
def cons (x : Int) (xs : SortedList) : SortedList := ⟨insert x xs.1, cons'.sorted _ _⟩

/-- Given a `SortedList`, returns the list of its unique elements. -/
def unique (l : SortedList) : List Int := l.val.unique l.property

end SortedList

namespace List

def sort (l : List Int) : SortedList := ⟨l.mergeSort, Sorted.mergeSort l⟩

end List
