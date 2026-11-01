/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM
import waterfall

set_option autoImplicit false
set_option tactic.hygienic false

open Cslib.Algorithms.Lean
#check TimeM

-- Analysis of merge sort
def merge : List ℕ → List ℕ → TimeM ℕ (List ℕ)
  | [], ys => return ys
  | xs, [] => return xs
  | x::xs', y::ys' => do
    ✓ let c := (x ≤ y)
    if c then
      let rest ← merge xs' (y::ys')
      return (x :: rest)
    else
      let rest ← merge (x::xs') ys'
      return (y :: rest)

def mergeSort (xs : List ℕ) : TimeM ℕ (List ℕ) :=  do
  if xs.length < 2 then return xs
  else
    let n := xs.length
    let half := n / 2
    let left :=  xs.take half
    let right := xs.drop half
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

-- # interpretation in each line
-- If the return type is a monad, say (`List ℕ`), then
-- `let sortedLeft ← mergeSort left`
-- This line means you can treat `sortedLeft` as type List ℕ and let notation tell Lean to put `sortedLeft` into a box
-- If the return type is not a monad, you can use normal `let` with `:=` notation.

#check mergeSort
#eval merge [1,2,3,10] [4,5]
#eval mergeSort [4,2,3,1]

-- Correctnes of Merge sort

@[simp, grind] def Nat.MinOfList (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- inductive predicate
inductive Sorted : List ℕ → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by
  cases hxs
  · simp
  · simp only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp]
    constructor
    · exact a_1
    · apply sorted_min at a_2
      grind
  · exact a_1

theorem sorted_is_preserved_by_min_cons {a : ℕ} {t : List ℕ} (hmin : a.MinOfList t)
  (ht : Sorted t) : Sorted (a :: t) := by
  exact Sorted.cons_min a t hmin ht


theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := by
  cases hxs
  · exact Sorted.nil
  · exact a_2
  · exact a_2

-- Exercise: Port your the proof of merge sort in the previous lectures into this proof.

theorem mem_either_merge (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ (merge xs ys).ret) : z ∈ xs ∨ z ∈ ys := by
  -- a much shorter proof uses `simp_all` and `grind` or `waterfall`
  -- try to see that the proof below closely corresponds to an informal proof
  fun_induction merge xs ys
  · simp at hz
    exact Or.inr hz
  · simp at hz
    exact Or.inl hz
  · simp at hz ⊢
    split_ifs at hz <;> simp at hz
    · cases hz
      · exact Or.inl (Or.inl h)
      · cases ih2 h
        · exact Or.inl (Or.inr h_1)
        · simp at h_1
          exact Or.inr h_1
    · cases hz
      · exact Or.inr (Or.inl h)
      · cases ih1 h
        · simp at h_1
          exact Or.inl h_1
        · exact Or.inr (Or.inr h_1)

theorem min_all_merge (x : ℕ) (xs ys : List ℕ)
(hxs : x.MinOfList xs) (hys : x.MinOfList ys) : x.MinOfList (merge xs ys).ret := by
  intro z hz
  cases mem_either_merge xs ys z hz
  · exact hxs z h
  · exact hys z h

theorem sorted_merge {l1 l2 : List ℕ} (hxs : Sorted l1)
  (hys : Sorted l2) : Sorted ((merge l1 l2).ret) := by
  fun_induction merge l1 l2
  · simpa
  · simpa
  · have hx := sorted_min hxs
    have hy := sorted_min hys
    simp
    split_ifs with hxy <;> simp
    · apply Sorted.cons_min
      · apply min_all_merge
        · exact hx
        · simp
          constructor
          · exact hxy
          · intro a ha
            grw [hxy]
            exact hy a ha
      · exact ih2 (sorted_suffix hxs) hys
    · simp at hxy
      apply Sorted.cons_min
      · apply min_all_merge
        · simp
          constructor
          · omega
          · intro a ha
            grw [hxy]
            exact hx a ha
        · exact hy
      · exact ih1 hxs (sorted_suffix hys)

-- Let's do this one as an example.
theorem MSMCorrect (xs : List ℕ) : Sorted (mergeSort xs).ret := by
  fun_induction mergeSort
  · simp only [TimeM.ret_pure]
    -- a compact way to match many cases:
    match x with
    | [] => exact Sorted.nil
    | [x] => exact Sorted.single x
    | y1::y2::ys => contradiction
  · simp only [TimeM.ret_bind]
    exact sorted_merge ih2 ih1

-- Time comlexity
def f (n : ℕ) : ℕ := 2 * n * Nat.clog 2 n + 1 -- f(n) = 2*n log n

-- Let's analyze time complexity

/- Helper lemma 1 -/
lemma merge_ret_eq_length (l1 l2 : List ℕ) : (merge l1 l2).ret.length = l1.length + l2.length := by
  fun_induction merge l1 l2 <;> simp
  · split_ifs <;> simp
    · rw [ih2, List.length]
      ring
    · rw [ih1, List.length]
      ring

/- Helper lemma 2 -/
lemma merge_time_le_length (l1 l2 : List ℕ) : (merge l1 l2).time ≤ l1.length + l2.length := by
  fun_induction merge l1 l2 <;> simp
  · split_ifs <;> simp
    · grw [ih2, List.length]
      omega
    · grw [ih1, List.length]
      omega

/- Helper lemma 3 -/
lemma mergeSort_eq_length (l : List ℕ) : (mergeSort l).ret.length = l.length := by
  fun_induction mergeSort l <;> simp
  · rw [merge_ret_eq_length, ih1, ih2]
    grind

example (xs : List ℕ) : (mergeSort xs).time < f (xs.length) := by
  fun_induction mergeSort xs
  · simp [f]
  · simp
    grw [ih1, ih2, merge_time_le_length, mergeSort_eq_length, mergeSort_eq_length]
    have hl : Nat.clog 2 left.length ≤ Nat.clog 2 ((x.length + 1) / 2) := by
      apply Nat.clog_mono_right
      grind
    have hr : Nat.clog 2 right.length ≤ Nat.clog 2 ((x.length + 1) / 2) := by
      apply Nat.clog_mono_right
      grind
    have hn : Nat.clog 2 x.length = Nat.clog 2 ((x.length + 1) / 2) + 1 :=
      Nat.clog_of_one_lt one_lt_two (by omega)
    have hsum : left.length + right.length = x.length := by
      grind
    unfold f
    grw [hl, hr, hn]
    rw [← hsum]
    grind
