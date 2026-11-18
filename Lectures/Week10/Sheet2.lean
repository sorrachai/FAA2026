/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic

set_option autoImplicit false

-- Typeclass as executable specifications and computability
-- When you write an alogrithm specification, you may want to test your spec.
-- Lean does not automatically give you an implementation.

/-!
## Decidable
Decidable connects propositions to computation.
In the standard library, Decidable is defined as follows.
-/

/-
class inductive Decidable (p : Prop) where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
-/

#check Decidable
#check Decidable.isTrue
#check Decidable.isFalse

-- Compare the types: a proposition lives in Prop; its decision lives in Type.
#check (3 < 8)             -- Prop
#check Decidable (3 < 8)   -- Type

-- We can construct decisions directly.
-- Think of `typeclass instance` as a term of the requested class type
instance : Decidable (3 < 8) := by
  apply Decidable.isTrue
  omega

instance : Decidable (8 < 3) := .isFalse (by omega)

/-!
Both true and false propositions can be decidable. An instance of Decidable p
does not necessarily contain a proof of p: it might contain a proof of ¬p.
-/

-- Exercise 1: construct this decision using isFalse and a proof.
-- Do not use inferInstance or the decide tactic for this exercise.
#check Decidable (9 ≤ 4)

-- Exercise 2: prove this
instance (p q : Prop) [Decidable p] [Decidable q] : Decidable (p ∧ q) := by
  expose_names
  cases inst <;> cases inst_1 <;> expose_names
  · apply Decidable.isFalse; tauto
  · apply Decidable.isFalse; tauto
  · apply Decidable.isFalse; tauto
  · apply Decidable.isTrue; tauto

/-!
## 2. Asking Lean to supply an instance

If a required value can be constructed by typeclass inference, we can ask
Lean to construct it using `inferInstance` in term mode or `infer_instace` in tactic mode.
The expected type tells Lean which instance to search for.
-/

instance : Decidable (3 < 8) := inferInstance
instance : Decidable (8 < 3) := inferInstance

#check (inferInstance : Decidable (3 < 8))
#synth Decidable (3 < 8)

-- inferInstanceAs states the type to synthesize explicitly.
-- Lean 4.33.1 also needs a known expected result type, supplied here by `:`.
#check (inferInstanceAs (Decidable (3 < 8)) : Decidable (3 < 8))

-- infer_instance is the tactic spelling; inferInstance is a term.
example : Decidable (3 < 8) := by
  infer_instance

-- Exercise: Prove this again
-- set_option trace.Meta.synthInstance.answer true in
instance (p q : Prop) [Decidable p] [Decidable q] : Decidable (p ∨ q) := inferInstance

-- Give a named predicate a decision procedure.

def InRange (n : Nat) : Prop :=
  10 ≤ n ∧ n < 20

-- sometimes inferInstance does not unfold definition
-- instance (n : Nat) : Decidable (InRange n) := by
--   unfold InRange
--   infer_instance

instance (n : Nat) : Decidable (InRange n) :=
 inferInstanceAs (Decidable (10 ≤ n ∧ n < 20))

-- #eval decide (InRange 15) -- true
-- #eval decide (InRange 25) -- false

-- The new instance now supports ordinary if-expressions.
def classify (n : Nat) : String :=
  if InRange n then "inside" else "outside"

#eval classify 15 -- "inside"


-- Classical reasoning can also supply Decidable p for any proposition p,
-- but that instance supplies no executable test.
noncomputable
instance (p q : Prop) : Decidable (p ∧ q → q) := by
  exact Classical.propDecidable (p ∧ q → q)

-- *Remark*:
-- Typeclasss resolution synthesizes an algorithm during the elaboration at compile time,
-- and then executes the algorithm at runtime.
-- Note: the elaborator translates the code you write into a term in Lean’s core language
-- because the kernel checks terms in that language

-- For more of Decidable, https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Decidable

-- Exercise:
variable {α β γ δ : Type*} [LinearOrder α] [LinearOrder β] [LinearOrder γ] [LinearOrder δ]
  {P : α → β → Prop} {M : γ → δ → Prop}

-- Forbidden matrix theory definition
-- A matrix M contains P as a submatrix if
-- ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b).
def Contains (P : α → β → Prop) (M : γ → δ → Prop) : Prop :=
  ∃ f : α → γ, StrictMono f ∧ ∃ g : β → δ, StrictMono g ∧ ∀ a b, P a b → M (f a) (g b)

-- Make a computable version of it
instance {P : α → β → Prop} {M : γ → δ → Prop} [DecidableRel P] [DecidableRel M]
    [DecidableLT α] [DecidableLT β] [DecidableLT γ] [DecidableLT δ]
    [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] : Decidable (Contains P M) := by sorry
