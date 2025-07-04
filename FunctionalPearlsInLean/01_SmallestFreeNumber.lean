/-
Problem:
Compute the smallest natural number not in a given finite set X of natural numbers.

Note:
The third solution uses the fact that any number occurs at most once.
-/
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

def isMinFree (x : ℕ) (xs : List ℕ) : Prop :=
  (x ∉ xs) ∧ ∀ y, y ∉ xs → x ≤ y

theorem eq_of_isMinFree {x y : ℕ} {xs : List ℕ} (h₁ : isMinFree x xs) (h₂ : isMinFree y xs) :
    x = y := by
  have : x ≤ y := h₁.right y h₂.left
  have : y ≤ x := h₂.right x h₁.left
  linarith

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
  let range := List.range (xs.length +1)
  let frees := range.filter (· ∉ xs)
  have nonempty : frees ≠ [] := by
    simp [frees]
    by_contra h
    push_neg at h
    have : range.length = xs.length + 1 := List.length_range
    have : range.length ≤ xs.length := subset_length_le_of_nodup range xs h List.nodup_range
    linarith
  frees.head nonempty

theorem minfree_naive_isMinFree (xs : List ℕ) : isMinFree (minfree_naive xs) xs := by
  simp [isMinFree, minfree_naive]
  generalize_proofs h₁
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp h₁
  simp [hx]; simp at hx; obtain ⟨h₁, h₂, h₃⟩ := hx
  use h₁; intro y hy; contrapose! hy; exact h₃ _ hy

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
def search (xs : Array Bool) : ℕ :=
  xs.takeWhile id |>.size

def accumArray (accum : β → α → β) (init : β) (size : ℕ) (xs : List (ℕ × α)) : Array β :=
  xs.foldl (fun arr (i,a) =>
    if _h : i < arr.size then
      arr.set i (accum arr[i] a)
    else
      arr)
  (Array.replicate size init)

def checklist (xs : List ℕ) : Array Bool :=
  let n := xs.length
  let pairs := xs.filter (· ≤ n) |>.zip (.replicate n true)
  accumArray .or false n pairs

def minfree_array : List ℕ → ℕ :=
  search ∘ checklist

theorem minfree_array_isMinFree (xs : List ℕ) : isMinFree (minfree_array xs) xs := by
  sorry

theorem minfree_array_is_minfree_naive : minfree_array = minfree_naive := by
  ext xs
  apply eq_of_isMinFree
  · exact minfree_array_isMinFree xs
  · exact minfree_naive_isMinFree xs

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
def List.boundedBy (xs : List ℕ) (bound : ℕ) : Prop :=
  xs.all (· ≥ bound)

def minfrom (a : ℕ) (xs : List ℕ) (bounded : xs.boundedBy a) (nodup : xs.Nodup) : ℕ :=
  if xs.isEmpty then
    a
  else
    let b := a + 1 + xs.length / 2
    let (us, vs) := xs.partition (· < b)
    have us_bounded : us.all (· < b) := by sorry
    have vs_bounded : vs.all (· ≥ b) := by sorry
    have us_bounded : us.boundedBy a := by sorry
    have vs_bounded : vs.boundedBy b := by sorry
    have us_nodup : us.Nodup := by sorry
    have vs_nodup : vs.Nodup := by sorry
    if _h : us.length = b - a then
      have : b > a := by sorry
      have : 0 < us.length := by sorry
      have : us.length + vs.length = xs.length := by sorry
      have : vs.length < xs.length := by calc
        vs.length = xs.length - us.length := Nat.eq_sub_of_add_eq' this
        _         < xs.length := by sorry
      minfrom b vs vs_bounded vs_nodup
    else
      have : us.length < xs.length := by calc
        us.length < b - a     := by sorry
        _         ≤ xs.length := by sorry
      minfrom a us us_bounded us_nodup
    termination_by xs.length

def minfree_DAC (xs : List ℕ) (nodup : xs.Nodup) : ℕ :=
  minfrom 0 xs (by simp [List.boundedBy]) nodup

theorem minfree_DAC_isMinFree (xs : List ℕ) (nodup : xs.Nodup) : isMinFree (minfree_DAC xs nodup) xs := by
  sorry

theorem minfree_DAC_is_minfree_naive (xs : List ℕ) (nodup : xs.Nodup) : minfree_DAC xs nodup = minfree_naive xs := by
  apply eq_of_isMinFree
  · exact minfree_DAC_isMinFree xs nodup
  · exact minfree_naive_isMinFree xs
