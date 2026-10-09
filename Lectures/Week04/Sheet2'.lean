/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
set_option tactic.hygienic false
set_option autoImplicit false

-- ## Strong induction and two-step induction
#check  Nat.strong_induction_on

def fib : Nat → Nat
  | 0   => 1
  | 1   => 1
  | n+2 => fib (n+1) + fib n

#eval fib 1
#eval fib 2
#eval fib 3
#eval fib 4
#eval fib 5

example (x : ℕ) : fib x ≤ 2^x := by
  induction x using Nat.strong_induction_on
  unfold fib
  split
  · simp
  · simp
  · rename' n_1 => n
    simp_all only [Nat.succ_eq_add_one, Order.lt_add_one_iff]
    rw [Nat.add_assoc n 1 1]
    simp only [Nat.reduceAdd]
    grw [a,a]
    · ring_nf
      simp only [Order.lt_two_iff, zero_le, pow_pos, mul_le_mul_iff_right₀, Nat.reduceLeDiff]
    · omega
    · omega

#check Nat.twoStepInduction

-- Exercise 3
example (x : ℕ) : fib x ≤ 2^x := by
  induction x using Nat.twoStepInduction
  · simp [fib]
  · simp [fib]
  · grw [fib, a_1, a]
    nth_rw 4 [←one_add_one_eq_two] 
    rw [←add_assoc, Nat.pow_add 2 (n + 1) 1, Nat.two_pow_succ n] 
    omega

-- Define the following recurrence relation
-- f (n) ≤ n + 2* f(n/2)
-- f (1) = 1

def f (n : ℕ) : ℕ :=
  if n = 0 then 0
  else 2*f (n/2) + n

def f_closed (n : ℕ) : ℚ := n * (Nat.log 2 n)+n

#eval (List.map f [0,1,2,3,4,5,6,7,8])
#eval (List.map f_closed [0,1,2,3,4,5,6,7,8])

-- Example
example (n : ℕ) : f (2^n) ≤ (n+1)*2^n := by
  induction n with
  | zero =>
    simp [f]
  | succ n ih =>
    unfold f
    simp only [Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, not_false_eq_true, and_true, ↓reduceIte]
    nth_rw 1 [Nat.pow_add_one']
    rw [Nat.mul_div_right (2 ^ n) (Nat.zero_lt_two)]
    grw [ih]
    ring_nf
    omega

-- Exercise 4: the cost of binary search
def g (n : ℕ) : ℕ :=
  if n = 0 then 0
  else g (n/2) + 1

def g_close (n : ℕ) : ℕ  :=  Nat.log 2 n + 1

#eval (List.map g [0,1,2,3,4,5,6,7,8,1000])
#eval (List.map g_close [0,1,2,3,4,5,6,7,8,1000])

example (n : ℕ) : g (2^n) ≤ n+1 := by 
  induction n with
  | zero => simp [g]
  | succ n ih =>
    rw [g] 
    split <;> simp [pow_succ, ih]
