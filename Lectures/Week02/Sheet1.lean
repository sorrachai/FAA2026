/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-!
## Universal quantifier (∀) and Existential (∃) Quantifiers
* `∀ x : α, P x` means for every element x of type α, the property P x holds.
   In Lean, this is the same as (x : α) → P x
* `∃ x : α, P x` means there exists some element x of type α such that P x holds
-/

-- Working with universal quantifier

/-!
  Another useage of `intro` tactic
  * `intro` -- to reduce a goal of the form `∀ x : ℕ , P(x)` to `P(x)` and obtain `x : ℕ` as a
    variable i.e., to prove for-all statement, let fix an arbitrary element x, and
    then we prove P(x). This is because, in Lean, ∀ x : N, P(x) is equivalent to (x :ℕ) →  P(x)
-/

def f (x : ℕ) := x = 0
#check f
example : (∀ x : ℕ, f x) ↔ ((x : ℕ) → f x) :=  by rfl

example : ∀ n : ℕ, n + 0 = n := by
  intro n
  rfl


/-! tactics for working with the existential quantifier
* `use` -- The use tactic is used to provide a witness for an existential statement: ∃ x, P x
* `obtain` -- When you have a hypothesis that states h : ∃ x, P x,
           -- you can use obtain to "extract" the witness x and its property P x from h
           -- so you can use them in your proof.
           -- obtain ⟨x, hx⟩ := h extracts witness and property from h: ∃ x, P x
           -- Use obtain ⟨a, ⟨b, c⟩⟩ := h for nested existentials
-/

example : ∃ n : ℕ, n + 3 = 7 := by
  use 4
example : ∃ n m : ℕ, n + m = 5 := by
  use 2,3


-- Definition of an even number.
def IsEven (n : ℤ) : Prop := ∃ k, n = 2 * k


-- If `n` is even, then `n` can be written as `k + k`.
example (n : ℤ) (h : IsEven n) : ∃ k, n = k + k := by
  -- Use `obtain` to get the number `n` and its properties from `h`.
  -- The syntax is: obtain ⟨a, ha⟩ := h
  unfold IsEven at h
  sorry

def IsOdd (n : ℤ) : Prop := ∃ k, n = 2 * k + 1

example (n:ℤ) (h : IsEven n) :  IsOdd (n+1) := by
  sorry

-- Exercise . Prove that the sum of two even numbers is even.
example (a b:ℤ) (h_a : IsEven a) (h_b : IsEven b) : IsEven (a + b) := by
  sorry
