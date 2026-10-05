/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false


/-!
## Induction Proofs
  **Goal:** Prove `∀ n : ℕ, P n`, where `P : ℕ → Prop` is a proposition indexed by a natural number.

  We can prove this by induction as follows:
  **Base case:** Prove `P 0`
  **Induction step:** Prove `∀ i : ℕ, P i → P (i+1)`

  In Lean, you can use the `induction` tactic to do so.
-/

-- Let's define a recursive function:
def I : ℕ → ℕ
  | 0 => 0
  | n + 1 => I n + 1

#eval [I 0, I 1, I 2]

example (n : ℕ) : I n = n := by
  induction n with
  | zero =>
    -- Base case: `I 0 = 0`
    rw [I]
  | succ i ih =>
    -- Induction step:
    --   assume `ih : I i = i`
    --   prove `I (i+1) = i+1`
    rw [I, ih]

/-
  New tactics:
  * `omega`: close the goal using linear arithmetic over `ℕ` and `ℤ`
  * `linarith`: close the goal using linear arithmetic over `ℚ` and `ℝ`
  * `ring`: close goals that are polynomial equations over commutative (semi)rings
-/

example (a b c : ℕ) (h1 : a ≤ b) (h2 : b + 1 ≤ c) : a < c := by
  omega

example (x : ℚ) (h : x ≥ 3 / 2) : 2 * x ≥ 3 := by
  linarith

example (a b : ℕ) : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
  ring


-- Exercise 1
def I2 : ℕ → ℕ
  | 0 => 0
  | n + 1 => I2 n + 2

#eval [I2 0, I2 1, I2 2]
example (n : ℕ) : I2 n = 2*n := by
  induction n with
  | zero =>
    unfold I2
    rfl
  | succ i ih =>
    unfold I2
    rw [ih]
    omega

example (n : ℕ) : Even (I2 n) := by
  induction n with
  | zero =>
    rw [I2]
    rw [Even]
    use 0
  | succ i ih =>
    unfold I2
    unfold Even
    rw [Even] at ih
    obtain ⟨r, hr⟩ := ih
    use (r+1)
    rw [hr]
    omega

-- Exercise 2
theorem even_or_odd (n : ℕ) : (∃ k, n = 2*k) ∨ (∃ k, n = 2*k+1) := by
  induction n with
  | zero =>
    left
    use 0
  | succ k ih =>
    cases ih with
    | inl ih_even =>
      obtain ⟨j, hj⟩ := ih_even
      right
      use j
      rw [hj]
    | inr ih_odd =>
      obtain ⟨j, hj⟩ := ih_odd
      left
      use j+1
      rw [hj]
      omega


-- Consider the following recursive sum definition
def S : ℕ → ℕ
  | 0 => 0
  | n + 1 => S n + (n + 1)

#eval [S 1, S 2, S 3]

-- Exercise 3
lemma Sn_two (n : ℕ) : 2*(S n) = n * (n + 1) := by
  induction n with
  | zero =>
    unfold S
    omega
  | succ k ih =>
    unfold S
    rw [Nat.mul_add]
    rw [ih]
    ring

example (n : ℕ) : (S n) = n * (n + 1)/2 -- natural number division
  := by
    rw [← Sn_two]
    omega


/-
  New tactics:
  * `have`: prove an intermediate fact that we can use later;
            syntax: `have h : P := ...` to introduce `h : P`
  * `grw`:  generalized rewriting; it works like `rw`, but can
            also rewrite using relations such as inequalities and
            set inclusion. It uses transitivity and information
            about which operations preserve order.
-/
example (a b c : ℕ) (h1 : a = b) (h2 : b = 2 * c) : a^2 = (2*c)^2 := by
  have h3 : a = 2*c := by
    -- New tactic state: subgoal `a = 2*c`
    omega
  rw [h3]

example (a b c : ℕ) (h1 : a ≥ b) (h2 : a = c) : (a - b + b)^2 = c^2 := by
  have h3 : a - b + b = a := by
    -- Note: if a ≤ b, then a - b = 0 in *natural number subtraction*,
    -- so this is not always true; we need h1 : a ≥ b
    omega
  rw [h3, ← h2]

example (A B C : Set ℕ) (h : A ⊆ B) : A ∪ C ⊆ B ∪ C := by
  grw [h]

example (a b c : ℕ) (h : a + 1 ≤ b) : a + c < b + c := by
  -- Initial goal: `a + c < b + c`
  grw [← h] -- grw [h] does not work as Lean tries to find a term (a+1)
  -- New goal: `a + c < a + 1 + c`
  omega


-- Consider the following factorial definition
def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

#eval [0!,1!,2!,3!,4!]

-- Exercise 4
lemma le_fact (n : ℕ) : 1 ≤ (n)! := by
  induction n with
  | zero =>
    trivial
  | succ n ih =>
    rw [factorial]
    grw [← ih]
    omega

#check Nat.mul_le_mul
#check pow_succ'

-- Exercise 5
example (n : ℕ) : 2^n ≤ (n+1)! := by
  induction n with
  | zero =>
    trivial
  | succ n ih =>
    unfold factorial
    grw [← ih]
    rw [pow_succ' 2 n]
    apply Nat.mul_le_mul
    · omega
    · rfl

/-!
## Induction for `n ≥ a`
  **Goal:** Prove `∀ n : ℕ, (n ≥ a) → P n`, where `P : ℕ → Prop` is a proposition indexed by a natural number.

  We can prove this by induction as follows:
  **Base case:** Prove `P a`
  **Induction step:** Prove `∀ i : ℕ, (i ≥ a) → (P i → P (i+1))`

  In Lean, you can use the `induction n, hn using Nat.le_induction` tactic to do so.
-/

-- The following lemma will be useful for the example
#check pow_succ

-- Example
example : ∀ n : ℕ, n ≥ 4 → 3 * n ≤ 2^n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    -- Goal: `3 * 4 ≤ 2^4`
    omega
  | succ k hk ih =>
    -- `hk : 4 ≤ k`
    -- `ih : 3 * k ≤ 2^k`
    -- Goal: `3 * (k + 1) ≤ 2^(k + 1)`
    rw [pow_succ]
    grw [← ih]
    omega

-- Below is an example proving it using ordinary `induction`
lemma shifted : ∀ n : ℕ, 3 * (n + 4) ≤ 2^(n + 4) := by
  intro n
  induction n with
  | zero =>
    omega
  | succ n ih =>
    rw [pow_succ]
    grw [← ih]
    omega

example : ∀ n ≥ 4, 3 * n ≤ 2^n := by
  intro n hn
  have h1 := shifted (n-4)
  have h2 : n - 4 + 4 = n := by omega -- natural number subtraction
  rewrite [h2] at h1
  exact h1


#check Nat.le_induction

-- There are many different variants of induction
#check Nat.decreasingInduction
#check Nat.div2Induction
