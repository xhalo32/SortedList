# SortedList

This repository aims to experiment with _formally verifying_ both **functional** and **imperative** programs using the Lean proof assistant.

## Structure

- `Main.lean` is a sample CLI for sorting lists. It also prints the unique values.
- `Basic.lean` contains the definition of `Sorted`:
    ```lean
    abbrev Sorted (l : List Int) := Pairwise (· ≤ ·) l
    ```
- `Unique.lean` defines a naïve implementation of `unique : List Int -> List Int` recursively.
- `Lemmas.lean` contains a lot of technical proofs about "sorted list theory"
- `SortedList.lean` defines a `SortedList` as a subtype of lists:
    ```lean
    def SortedList := { l : List Int // l.Sorted }
    ```
    along with some API for sorted lists
- `Decidable.lean` investigates how to decide when a list is sorted and its implications.
- `Invariant.lean` experiments with the new Std.Do API.
- `Imperative.lean` defines `unique` as an imperative program:
    ```lean
    def unique (xs : List Int) : Id (List Int) := do
        let mut c : Option Int := none -- previous x in the list
        let mut out := [] -- output of the function

        for x in xs do
            if some x != c then
            out := out ++ [x]
            c := some x

        out
    ```
    and proves that it satisfies the following specification:
    ```lean
    ⦃⌜Sorted l⌝⦄ unique l ⦃⇓r => l ⊆ r ∧ StrictSorted r⦄
    ```
    which states that given a sorted list as input, `unique` returns a list with the following properties:
    - every element in the input is in the output, and
    - the output is strictly increasing (or equivalently, doesn't contain duplicates and is sorted).

## Getting started

1. Install Lean (`nix-shell -p elan` and `elan default stable`)
2. Run `lake exe sortedlist`

Sample run:

```
1 1 2 2 3
Your input: [1, 1, 2, 2, 3]
Unique elements: [1, 2, 3]
1 2 3 4 1
Your input: [1, 2, 3, 4, 1]
Input was not sorted at index 4
Your input (sorted): [1, 1, 2, 3, 4]
Unique elements: [1, 2, 3, 4]
```

## Inspiration

The imperative aspect is inspired by the very interesting blog post by Markus Himmel: [My first verified (imperative) program](https://markushimmel.de/blog/my-first-verified-imperative-program/).