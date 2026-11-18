/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false

-- Executable Prop
/-!
## From a specification to an executable checker

We can state a property in `Prop` and use it in proofs before choosing
how to check it. A computable `Decidable` instance lets us run the check.


`Final remark`:
In Lean, you may use classical reasoning to prove that a witness exists during the proof of a Prop.
Given `h : ∃ x, P x`, `Classical.choose h` selects a witness nonconstructively.
To obtain a witness at runtime, you need to design an algorithm that computes it.
-/

-- Mathlib's existing checker
#eval decide (IsSquare (49 : ℕ)) -- true

-- Our specification
def has_sqrt (n : ℕ) : Prop := ∃ m : ℕ, m * m = n

-- The integer square root gives us the candidate to check.
theorem sqrt_test_iff (n : ℕ) :
    n.sqrt * n.sqrt = n ↔ has_sqrt n :=
  (Nat.exists_mul_self n).symm

-- Note: (n.sqrt * n.sqrt = n) is decidable.

-- Use the equivalence to turn the equality test into a decision procedure.
instance (n : ℕ) : Decidable (has_sqrt n) :=
  decidable_of_iff (n.sqrt * n.sqrt = n) (sqrt_test_iff n)

#eval (has_sqrt 0)  -- true
#eval (has_sqrt 49) -- true
#eval (has_sqrt 50) -- false

example : has_sqrt 49 := by decide +kernel
example : ¬ has_sqrt 50 := by decide +kernel

-- Witness extraction:
def sqrtWitness (n : ℕ) (h : has_sqrt n) : {m : ℕ // m * m = n} :=
  ⟨n.sqrt, (sqrt_test_iff n).mpr h⟩

-- Sorting Spec
def SortSpec {α : Type} [LE α] (xs ys : List α) : Prop :=
  ys.Pairwise (· ≤ ·) ∧ xs.Perm ys

-- A proof of the specification gives both properties directly.
example {α : Type} [LE α] (xs ys : List α) (h : SortSpec xs ys) :
    xs.Perm ys :=
  h.2

section
variable {α : Type} [LE α] [DecidableLE α] [DecidableEq α]
instance (xs ys : List α) : Decidable (SortSpec xs ys) := by
  unfold SortSpec
  infer_instance
end

#eval (SortSpec [3, 1, 3] [1, 3, 3]) -- true
#eval (SortSpec [3, 1, 3] [1, 3])    -- false: lost a 3
#eval (SortSpec [3, 1, 3] [3, 3, 1]) -- false: out of order

-- Another example
def HasHalf (n : Nat) : Prop := ∃ k : Nat, n = 2 * k

theorem mod_two_eq_zero_iff (n : Nat) : n % 2 = 0 ↔ HasHalf n := by
  constructor
  · intro h
    exact ⟨n / 2, by omega⟩
  · rintro ⟨k, hk⟩
    omega

instance (n : Nat) : Decidable (HasHalf n) :=
  decidable_of_iff (n % 2 = 0) (mod_two_eq_zero_iff n)

#eval decide (HasHalf 14) -- true
#eval decide (HasHalf 15) -- false

example : HasHalf 14 := by decide

-- Exercise
def IsListMin {α : Type} [LE α] (m : α) (xs : List α) : Prop :=
  m ∈ xs ∧ ∀ x ∈ xs, m ≤ x

instance {α : Type} [LE α] [DecidableEq α] [DecidableLE α]
    (m : α) (xs : List α) : Decidable (IsListMin m xs) := by
  sorry

-- Predict each result, then uncomment after completing the instance.
-- #eval decide (IsListMin 2 [4, 2, 7])
-- #eval decide (IsListMin 1 [4, 2, 7])
-- #eval decide (IsListMin 4 [4, 2, 7])

-- Another exercise
def HasLaterSlot (now deadline : Nat) : Prop :=
  ∃ slot : Nat, now < slot ∧ slot ≤ deadline

theorem lt_iff_hasLaterSlot (now deadline : Nat) :
    now < deadline ↔ HasLaterSlot now deadline := by
  sorry

instance (now deadline : Nat) : Decidable (HasLaterSlot now deadline) := by
  sorry

-- #eval decide (HasLaterSlot 5 6)  -- true
-- #eval decide (HasLaterSlot 5 5)  -- false
