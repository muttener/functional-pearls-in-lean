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
import Mathlib.Tactic.Linarith

theorem subset_length_le_of_nodup [BEq α] [LawfulBEq α] (xs ys : List α) (subset : xs ⊆ ys) (nodup : xs.Nodup) :
    xs.length ≤ ys.length := by
  match xs with
  | [] => exact Nat.zero_le ys.length
  | x :: xs' =>
    have x_in_ys : x ∈ ys := subset List.mem_cons_self
    let ys' := ys.erase x
    have subset' : xs' ⊆ ys' := by
      intro a ha
      have a_ne_x : a ≠ x := by aesop
      have : a ∈ ys := subset (List.mem_cons_of_mem x ha)
      rwa [List.mem_erase_of_ne a_ne_x]
    have nodup' : xs'.Nodup := List.Nodup.of_cons nodup
    have : xs'.length ≤ ys'.length := subset_length_le_of_nodup xs' ys' subset' nodup'
    have : 0 < ys.length := List.length_pos_of_mem x_in_ys
    have : ys'.length + 1 = ys.length := by
      rw [List.length_erase_of_mem x_in_ys]
      apply Nat.sub_add_cancel
      linarith
    rw [List.length_cons]
    linarith

def minfree_naive (xs : List ℕ) : ℕ :=
  let interval := List.range (xs.length +1)
  let diff := interval.filter (· ∉ xs)
  have nonempty : diff ≠ [] := by
    simp [diff]
    by_contra h
    push_neg at h
    have : interval.length = xs.length + 1 := List.length_range
    have : interval.length ≤ xs.length := subset_length_le_of_nodup interval xs h List.nodup_range
    linarith
  diff.head nonempty

-- def minfree_naive' (xs : Array ℕ) : ℕ :=
--   let interval := Array.range (xs.size +1)
--   let diff := interval.filter (· ∉ xs)
--   have : 0 < diff.size := by
--     by_contra h
--     simp [diff] at h
--     have : diff.isEmpty := by
--       simp [diff]
--       assumption
--     have : ∀ i < xs.size + 1, i ∈ xs := by
--       intro i hi
--       have : i ∈ interval := by aesop
--       have : i ∉ diff := by aesop
--       by_contra nhi
--       aesop
--     have : xs.size ≥ xs.size + 1 := by
--       sorry
--     linarith
--   diff[0]

-- def minfree_naive'' (xs : Finset ℕ) : ℕ :=
--   let interval := Finset.range (xs.card + 1)
--   let diff := interval \ xs
--   have : 1 ≤ diff.card := calc
--     1 ≤ interval.card - xs.card := by simp_all only [Finset.card_range, Nat.add_sub_cancel_left, le_refl, interval]
--     _ ≤ (interval \ xs).card := by exact Finset.le_card_sdiff xs interval
--     _ ≤ diff.card := by simp_all only [le_refl, interval, diff]
--   have : diff.Nonempty := by
--     exact Finset.card_pos.mp this
--   diff.min' this

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
def search (xs : List Bool) : ℕ :=
  xs.takeWhile id |>.length

def accumList (accum : β → α → β) (init : β) (size : ℕ) (xs : List (ℕ × α)) : List β :=
  -- TODO: check if using arrays instead of lists actually boosts performance.
  xs.foldl (fun arr (i,a) =>
    if _h : i < arr.size then
      arr.set i (accum arr[i] a)
    else
      arr)
  (Array.replicate size init)
  |>.toList

def checklist (xs : List ℕ) : List Bool :=
  let n := xs.length
  let pairs := xs.filter (· ≤ n) |>.zip (.replicate n true)
  accumList .or false n pairs

def minfree_array : List ℕ → ℕ :=
  search ∘ checklist

-- Divide and conquer solution
/-
Properties (for lists):
  (as ++ bs) \\ cs = (as \\ cs) ++ (bs \\ cs)
  as \\ (bs ++ cs) = (as \\ bs) \\ cs
  (as \\ bs) \\ cs = (as \\ cs) \\ bs
  -- Suppose now that as and vs are disjoint and that bs and us are also disjoint.
  (as ++ bs) \\ (us ++ vs) = (as \\ us) ++ (bs \\ vs)
  [0 .. ] \\ xs = ([0 .. b−1] \\ us) ++ ([b .. ] \\ vs)
    where (us, vs) = partition (< b) xs
  head (xs ++ ys) = if null xs then head ys else head xs
  -- Suppose us consists of disticts numbers smaller than b.
  null ([0 .. b−1] \\ us ≡ length us == b

Haskell:
  -- Idea: for some b, it ought to be:
  minfree :: [Nat] → Nat
  minfree xs = if null ([0 .. b−1] \\ us)
    then head ([b .. ] \\ vs)
    else head ([0 .. ] \\ us)
    where (us, vs) = partition (< b) xs

  -- Suppose every element of xs is greater than or equal to a.
  minfrom :: Nat → [Nat] → Nat
  minfrom a xs = head ([a .. ] \\ xs)

  -- Refactor using minfrom.
  minfree xs = minfrom 0 xs
  minfrom a xs
    | null xs            = a
    | length us == b − a = minfrom b vs
    | otherwise          = minfrom a us
      where (us, vs) = partition (< b) xs
            b        = a + 1 + (length xs) div 2

  -- Optimize to avoid repeatedly computing length.
  minfree xs = minfrom 0 (length xs, xs)
  minfrom a (n, xs)
    | n 0       = a
    | m b − a   = minfrom b (n − m, vs)
    | otherwise = minfrom a (m, us)
      where (us, vs) = partition (< b) xs
            b        = a + 1 + n div 2
            m        = length us
-/
-- def minfrom (a : ℕ) (xs : Array ℕ) (bound : ∀ x ∈ xs, a ≤ x) (nodup : ) : ℕ :=
--   if xs.isEmpty then
--     a
--   else
--     let b := a + 1 + xs.size / 2
--     let (us, vs) := xs.partition (· < b)
--     if us.size = b - a then
--       minfrom b vs sorry
--     else
--       minfrom a us sorry
--   termination_by xs.size
--   decreasing_by
--     show vs.size < xs.size
--     have h : us.size + vs.size = xs.size := by
--       sorry
--     have : us.size > 0 := sorry
--     linarith
--     show us.size < xs.size
--     have h : us.size < b - a := by
--       sorry

--     sorry

-- def minfree_DAC (xs : Array ℕ) : ℕ :=
--   minfrom 0 xs
