/-
Problem:
Compute the smallest natural number not in a given finite set X
of natural numbers.

Note:
The third solution uses the fact that any number occurs at most once.
To compare all algorithms, this will be assumed for all of them.
-/

-- Naive solution
/-
The original Haskell code is very elegant:
  minfree :: [Nat] → Nat
  minfree xs = head ([0 .. ] \\ xs)
Lean is a strict language, while Haskell is lazy;
hence the approach using infinite lists will not work.
In fact, the original solution allows infinite lists as input as well,
so termination is not even guaranteed.

The code below follows the original one in spirit.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max

def minfree_naive (xs : Finset ℕ) : ℕ :=
  let interval := Finset.range (xs.card + 1)
  let diff := interval \ xs
  have : 1 ≤ diff.card := calc
    1 ≤ interval.card - xs.card := by simp_all only [Finset.card_range, Nat.add_sub_cancel_left, le_refl, interval]
    _ ≤ (interval \ xs).card := by exact Finset.le_card_sdiff xs interval
    _ ≤ diff.card := by simp_all only [le_refl, interval, diff]
  have : diff.Nonempty := by
    exact Finset.card_pos.mp this
  diff.min' this

-- Array based solution
/-
Haskell:
  minfree :: [Nat] → Nat
  minfree = search · checklist

  search :: Array Int Bool → Int
  search = length · takeWhile id · elems

  checklist :: [Int] → Array Int Bool
  checklist xs = accumArray (∨) False (0, n)
    (zip (filter (≤ n) xs) (repeat True ))
      where n = length xs
-/
def search (xs : Array Bool) : ℕ :=
  xs.takeWhile id |>.size

def checklist (xs : Finset ℕ) : Array Bool :=
  -- TODO: this construction is probably quadratic, not linear!
  Array.ofFn (n := xs.card) (fun n => n ∈ xs)

def minfree_array : Finset ℕ → ℕ :=
  search ∘ checklist

-- Divide and conquer solution
