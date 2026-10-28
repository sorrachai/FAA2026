/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Cslib.Algorithms.Lean.TimeM -- import cslib's time tracking
import waterfall

set_option autoImplicit false
set_option tactic.hygienic false

-- # Q: How to analyze time complexity?
-- We will instrument the code to track the time.
-- However, we do not want to interfere the correctness analysis.
-- We learn an elegant way to do this using Moad
-- # Separation of concerns: the correctness proof and running time proof should not interfere to each other

open Cslib.Algorithms.Lean
-- Let's look into TimeM
#check TimeM

def len : List ℕ →  ℕ
| [] => 0
| _ :: xs => 1 + len xs

-- lenT with do notations
def lenT : List ℕ → TimeM ℕ ℕ
| [] => return 0 -- produce ⟨0, 0⟩
| _ :: xs => do
    ✓ -- add a tick ⟨unit, 1⟩; discard its unit result, keep its cost
    let len_xs ← lenT xs -- get len_xs from the recursive result ⟨len_xs, t'⟩;
                        -- include t' in the accumulated cost
    ✓ return (1 + len_xs) -- add another tick, then produce ⟨1 + len_xs, 0⟩
-- The entire do block produces: ⟨1 + len_xs, 1 + t' + 1⟩

-- Example usage
#eval lenT []
#eval lenT [3,2,5]
#eval lenT [1,2,3,4,5]

theorem lenT_correctness (xs : List ℕ) : (lenT xs).ret = len xs := by
  induction xs
  · rfl
  · simp only [lenT, bind_pure_comp, TimeM.ret_bind, TimeM.ret_map]
    rw [tail_ih]
    rfl

theorem lenT_time (xs : List ℕ) : (lenT xs).time = 2 *(len xs) := by
  induction xs
  · rfl
  · simp only [lenT, bind_pure_comp, TimeM.time_bind, TimeM.time_tick, TimeM.time_map]
    rw [tail_ih]
    have: len (head :: tail) = 1 + len tail := rfl
    rw [this]
    omega

example (xs : List ℕ) : (lenT xs).ret = len xs := by waterfall
example (xs : List ℕ) : (lenT xs).time = 2 * (len xs) := by waterfall

-- ============================================================================
-- EXERCISE 1: Sum of a list
-- ============================================================================
-- Implement sumT that computes the sum of a list with time tracking
-- Each recursive call should cost 1 time unit
-- Expected time complexity: n where n is the length of the list

def sum : List ℕ → ℕ
| [] => 0
| x :: xs => x + sum xs

def sumT : List ℕ → TimeM ℕ ℕ
| [] => return 0
| x :: xs => sorry

theorem sumT_correctness (xs : List ℕ) : (sumT xs).ret = sum xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => sorry

-- Exercise: Prove time complexity
theorem sumT_time (xs : List ℕ) : (sumT xs).time = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => sorry

-- ============================================================================
-- EXERCISE 2: Reverse a list
-- ============================================================================
-- Implement reverseT that reverses a list with time tracking
-- Each cons operation should cost 1 time unit
-- Time complexity: n² where n is the length of the list

def reverse : List ℕ → List ℕ
| [] => []
| x :: xs => reverse xs ++ [x]

def reverseT : List ℕ → TimeM ℕ (List ℕ)
| [] => return []
| x :: xs => sorry

-- Prove correctness
theorem reverseT_correctness (xs : List ℕ) : (reverseT xs).ret = reverse xs := by
  sorry

-- Hint: You'll need a helper lemma about the time of append
theorem reverseT_time_quadratic (xs : List ℕ) :
  ∃ c, (reverseT xs).time ≤ c * xs.length * xs.length := by
  use 1
  simp only [one_mul]
  induction xs with
  | nil => simp [reverseT]
  | cons x xs ih =>
      sorry

-- ============================================================================
-- EXERCISE 3: Tail-recursive reverse with accumulator
-- ============================================================================
-- Implement a tail-recursive reverse using an accumulator
-- Each step should cost 1 time unit
-- Expected time complexity: n (linear, much better than reverseT!)

def reverseTailT : List ℕ → List ℕ → TimeM ℕ (List ℕ)
| [], acc => sorry
| x :: xs, acc => sorry

def reverseTail : List ℕ → List ℕ → List ℕ
| [], acc => acc
| x :: xs, acc => reverseTail xs (x :: acc)

-- Prove correctness
theorem reverseTailT_correctness (xs acc : List ℕ):
  (reverseTailT xs acc).ret = reverseTail xs acc := by
  sorry

-- Prove linear time complexity
theorem reverseTailT_time (xs acc : List ℕ):
  (reverseTailT xs acc).time = xs.length := by
  sorry
