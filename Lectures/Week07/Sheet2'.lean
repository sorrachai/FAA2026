/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM
import waterfall


-- Analysis of Insertion Sort
namespace mysorting

-- Define Insertion Sort
def insert (x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | [] => [x]
  | y :: ys =>
    if x ≤ y then x :: xs
    else y :: insert x ys

-- split_ifs tactic, split tactics

def IS : List ℕ → List ℕ
 | [] => []
 | x :: xs =>
 let ret := IS xs
 insert x ret

#eval IS [5,10,2,3,9]
-- Let's state a sorted property using type

@[simp] abbrev Nat.leqAll (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- Property of sortedness
inductive sorted : List ℕ → Prop
| empty : sorted []
| min (a : ℕ ) (t : List ℕ) : Nat.leqAll a t → sorted t → sorted (a :: t)

theorem sorted_sublist (y : ℕ) (ys : List ℕ) (h : sorted (y :: ys))
  : Nat.leqAll y ys ∧ sorted ys := by
  waterfall

theorem sorted_xyys_of_sorted_yys (x y : ℕ) (ys : List ℕ) (h_1 : x ≤ y) (h : sorted (y :: ys)) :
  sorted (x :: y :: ys) := by waterfall

theorem sorted_y_insert (x y : ℕ) (ys : List ℕ) (h_1 : y < x) (h2 : sorted (insert x ys))
  (h : Nat.leqAll y ys) : sorted (y :: insert x ys) := by waterfall [sorted_xyys_of_sorted_yys]

lemma insert_into_sorted (x : ℕ) (xs : List ℕ) (h : sorted xs) : sorted (insert x xs) := by
  waterfall [sorted_y_insert]

lemma correctness (xs : List ℕ) : sorted (IS x) := by
  waterfall [insert_into_sorted,sorted_y_insert]

-- Time complexity
open Cslib.Algorithms.Lean
#check TimeM


-- def insert (x : ℕ) (xs : List ℕ) : List ℕ :=
--   match xs with
--   | [] => [x]
--   | y :: ys =>
--     if x ≤ y then x :: xs
--     else y :: insert x ys

-- Define Insertion Sort with TimeM
def insertT (x : ℕ) (xs : List ℕ) : TimeM ℕ (List ℕ) :=
  match xs with
  | [] => return [x]
  | y :: ys => do
    ✓ let c := x ≤ y
    if c then return (x :: xs)
    else
    let ret ← insertT x ys
    return  y :: ret

-- # interpretation in each line
-- If the return type is a monad, say (`List ℕ`), then
-- `let ret ← insertT left`
-- This line means you can treat `ret` as type `List ℕ` and
-- let notation tell Lean to put `sortedLeft` into a box
-- If the return type is not a monad, you can use normal `let` with `:=` notation.

def IST : List ℕ → TimeM ℕ (List ℕ)
 | [] => return []
 | x :: xs =>  do
 let rest ← IST xs
 insertT x rest

#eval IST [3,2,1,100,5,100,90,80]

theorem insert_eq_insertT (x : ℕ) (xs : List ℕ) : (insertT x xs).ret = insert x xs := by waterfall

theorem correct_IST (xs : List ℕ) : (IST xs).ret = IS xs := by
  fun_induction IST
  · rfl
  · expose_names
    simp only [TimeM.ret_bind, IS]
    rw [ih1]
    apply insert_eq_insertT

#eval IST [1,2,3,4]

theorem time_insert (x : ℕ) (xs : List ℕ) : (insertT x xs).time ≤ (xs.length) := by
  fun_induction insertT <;> grind

@[grind =] theorem insert_length_eq (y : ℕ) (ys : List ℕ) :
  (insertT y ys).ret.length = ys.length + 1  := by
  fun_induction insertT <;> grind

lemma list_length (xs : List ℕ) : (IST xs).ret.length = xs.length := by
  fun_induction IST <;> grind

theorem time_IS (xs : List ℕ) : (IST xs).time ≤ (xs.length) * (xs.length) := by
  fun_induction IST
  · rfl
  · expose_names
    simp_all only [TimeM.time_bind, List.length_cons]
    grw [time_insert,ih1, list_length]
    ring_nf
    omega

end mysorting
