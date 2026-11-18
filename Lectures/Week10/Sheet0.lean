/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false
set_option tactic.hygienic false

-- Q: How do we select an element from ∃ x , P x statement?
def has_sqrt (n : ℕ) : Prop := ∃ m : ℕ, m * m = n

-- Lean has a universal way to extract the witness using axiom of choice:
-- The side effect : non-constructive
noncomputable
def sqrt_if_perfect (n : ℕ) (h : has_sqrt n) : ℕ :=
  --simp [has_sqrt] at h
  --obtain ⟨m,hm⟩ := h
    h.choose
-- obtain
-- sorry --? How to extract the witness

-- Alternatively, one can write an algorithm to output the witness explicitly. We will see how.

-- In Lean, you can use `Classical.choose`.
#check Classical.choose
#check Classical.choose_spec

noncomputable def witness_perfect (n : ℕ) (h : has_sqrt n) : ℕ := h.choose
def witness_perfect_spec (n : ℕ) (h : has_sqrt n) := h.choose_spec

#check witness_perfect
#check witness_perfect_spec

-- Side effect: this choose function relies on the axiom of choice, require marking
-- the corresponding function `noncomputable`: This means Lean cannot automatically find the executable code.

-- Sorts are the classifications of types.
-- We can think of `Sort u` as a type with differnet level of universes.
-- The first level of the universe is `Sort 0` which is `Prop`.

#check Sort 0
 -- is named as Prop
#check Sort 1 -- is named as Type
#check Sort 2 -- Types of types
#check Sort 3

#print Classical.choice

-- Classical.choice takes a proof h that a type α is nonempty and produces an element of α.
-- However, since h lives in Prop, it doesn’t provide any constructive information about which element exists.
-- As a result, Classical.choice is noncomputable — it asserts existence but gives no way to actually find the element.

theorem Nat.Nonempty : Nonempty ℕ := by use 0

#check Classical.choice Nat.Nonempty

noncomputable def arbitraryNat : ℕ := Classical.choice Nat.Nonempty

-- In the analysis of algorithms we do not require computability, and using this can be more conveinent.
-- If required, one can remove computatbility assumption by
-- (1) directly implement an algorithm that outputs it, or
-- (2) show that a type if finite

#check Fintype.choose

-- In this case, obtain only works when we work on some proposition
def some_prop : Prop := 1 = 1

def sqrt_if_perfect2 (n : ℕ) (h : has_sqrt n) : some_prop := by
  obtain ⟨n,nh⟩ := h
  sorry

-- The key architectural decision in Lean: Prop is proof-irrelevant and computationally erased.
-- The `obtain` tactic only work in the Prop (i.e., proof mode).
-- whereas `Classical.choose` lifts from Prop to Type.

#check Classical.choose
-- Classical.choose : {α : Sort u} → (∃ x, p x) → α
--                                      ^^^^^^     ^^
--                                      Prop       Type!

-- Upshot:
-- We can use obtain tactics to extract witness in the proof mode.
-- To go outside of proof mode, use Classical.choose to extract witness as a type and use Classical.choose_spec to access its property
-- Or define an algorithm that computs it.

-- Classical.choice = function that returns an arbitrary element of a nonempty type
-- Classical.choose = function that returns a witness given a proof of an ∃

-- In this sheet, we walk through bitonic arrays as exercises.

def Bitonic (f : ℕ → ℤ) (n : ℕ) : Prop :=
  ∃ k,  k < n ∧
    StrictMonoOn f (Set.Icc 0 k) ∧   -- nondecreasing on [0,k]
    StrictAntiOn f (Set.Ici k)       -- nonincreasing on [k, ∞)

-- A "bitonic" array is an array that strictly increases and then strictly decreases,
-- like [1, 4, 8, 10, 5, 2]. The goal is to find the "peak" element (10). The search logic is:
-- Look at mid and mid+1.
-- If arr.get mid < arr.get (mid+1), the peak must be in the right half.
-- If arr.get mid > arr.get (mid+1), the peak is in the left half (and mid could be it).

structure BitonicSortedArrayFun (n : ℕ) where
  get : ℕ → ℤ
  size : ℕ := n
  bitonic: Bitonic get n

-- Example 1
def example1 : BitonicSortedArrayFun 5 := ⟨
  fun i => if i ≤ 2 then i else 4 - i,  -- get
  5,                                    -- size (optional since default is n)
  by
    simp [Bitonic]
    use 2
    simp [StrictMonoOn,StrictAntiOn]
    bound
⟩

#check example1

-- Example 2:
def example2 : BitonicSortedArrayFun 100 where
  get := fun i => 2-i
  bitonic := by
    use 0
    simp [StrictMonoOn,StrictAntiOn]

-- This property appears in the analysis, marking noncomputable is fine.
noncomputable
def BitonicSortedArrayFun.peak_idx {n :ℕ} (arr: BitonicSortedArrayFun n) := (arr.bitonic).choose

lemma BitonicSortedArrayFun.peak_idx_spec {n :ℕ} (arr: BitonicSortedArrayFun n) : arr.peak_idx < n ∧
  StrictMonoOn arr.get (Set.Icc 0 arr.peak_idx) ∧ StrictAntiOn arr.get (Set.Ici arr.peak_idx) := (arr.bitonic).choose_spec

-- The followings consist of exercises to get familiar with choose and choose_spec

-- Example 1: Prove the peak index is bounded
lemma BitonicSortedArrayFun.peak_idx_lt_size {n : ℕ} (arr : BitonicSortedArrayFun n) :
    arr.peak_idx < n := by
    have:= arr.peak_idx_spec
    exact this.1

#print axioms BitonicSortedArrayFun.peak_idx_lt_size
#check propext
#check Classical.choice

-- Exercise 2: Prove monotonicity up to peak
lemma BitonicSortedArrayFun.mono_before_peak {n : ℕ} (arr : BitonicSortedArrayFun n) :
    StrictMonoOn arr.get (Set.Icc 0 arr.peak_idx) := by sorry

-- Exercise 3: Prove that any element before peak is less than peak value
-- Hint: Combine choose_spec with StrictMonoOn properties
lemma BitonicSortedArrayFun.before_peak_lt_peak {n : ℕ} (arr : BitonicSortedArrayFun n)
    (i : ℕ) (hi : i < arr.peak_idx) :
    arr.get i < arr.get arr.peak_idx := by sorry

-- Exercise 4: Prove that any element after peak is less than peak value
lemma BitonicSortedArrayFun.after_peak_lt_peak {n : ℕ} (arr : BitonicSortedArrayFun n)
    (i : ℕ) (hi : i > arr.peak_idx) :
    arr.get i < arr.get arr.peak_idx := by sorry
