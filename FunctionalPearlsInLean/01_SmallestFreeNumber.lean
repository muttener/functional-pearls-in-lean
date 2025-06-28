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

def minfree (xs : Finset ℕ) : ℕ :=
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

-- Divide and conquer solution
