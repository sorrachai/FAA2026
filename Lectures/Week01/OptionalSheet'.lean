/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Basil Rohner, Olivier Fischer, Sorrachai Yingchareonthawornchai
-/
import Mathlib.Tactic

/-!
# Optional Homework

This homework is optional and not graded. The sheet gives a more
in-depth treatment of Lean's **term**-mode, and working through it
will give you a better understanding of how Lean works under the hood.
-/

section Logic

/-
Most proofs that you have seen until now in the lecture were
written using **tactics**. Tactics are commands in Lean which
automate the construction of Lean proofs and allow you to
write proofs closer to how one typically writes informal proofs.
In Lean, you  enter **tactic**-mode by adding a `by` before the proof.

Instead of tactics, you can also explicitly construct
the proof terms in **term**-mode. Lean treats propositions
as types which have type `Prop` (e.g., `P ∧ Q : Prop`) and
proofs as terms that inhabit that type (e.g., `p : P ∧ Q`).
Suppose we have propositions `P`, `Q`, and `R`:
-/

variable (P Q R : Prop)

/-
To prove a conjunction (e.g., `P ∧ Q : Prop`) we need to
provide Lean with a pair of proof terms: one for`P : Prop` and one for `Q : Prop`.
Lean implements a construct `And` with one constructor for that purpose.
Given a conjunction we can obtain proof terms for the conjuncts
by projecting to the components of the pair. Examples:
-/

#check And.intro -- And.intro {a b : Prop} (left : a) (right : b) : a ∧ b

example (p : P) (q : Q) : P ∧ Q :=
  And.intro p q

example (p : P) (q : Q) : P ∧ Q :=
  -- if the constructor can be inferred, Lean allows anonymous constructors
  ⟨p, q⟩

example (pq : P ∧ Q) : P :=
  pq.1

example (pq : P ∧ Q) : Q :=
  pq.2

/-
To prove a disjunction (e.g., `P ∨ Q : Prop`) we need to
provide Lean with either a proof term for `P : Prop` or
`Q : Prop`. The `Or` construct implements two constructors,`Or.inl` and `Or.inr`,
which take a proof term for the left and right disjunct respectively.
To obtain either of the proof terms of the  disjuncts we can match
on the constructor of the `pq : P ∨ Q` construct. Examples:
-/

#check Or.inl
#check Or.inr

example (p : P) : P ∨ Q :=
  Or.inl p

example (pq : P ∨ Q) : Q ∨ P :=
  match pq with
  -- if pq was constructed from Or.inl, we get `p : P`
  | Or.inl p => Or.inr p
  -- if pq was constructed from Or.inr, we get `q : Q`
  | Or.inr q => Or.inl q

/-
To prove an implication (e.g., `P → Q : Prop`) we need to
provide a function which takes in a proof term for `P : Prop`
and, using `p : P`, constructs a proof term for `Q : Prop`.
Given a proof `pq : P → Q` and a proof `p : P`, we can obtain
a proof `q : Q` by applying the function `pq` on `p`. Examples:
-/

example : P → P :=
  fun x => x

example (p : P) (pq : P → Q) := pq p

/-
Negation `¬P : Prop` is simply defined as `P → False : Prop`, where
`False : Prop` is an empty type (which can therefore not be proven as it
contains no proof terms). Often, when propositions involve negation, we
use `False.elim` which takes a proof term `f : False` and produces a proof term
`p : P` for any proposition `P : Prop` since everything follows from `False`.
-/

-- To prove `False` with `P` and `¬ P`, we apply `not_p` (type `P → False`) to `p` (type `P`)
theorem proving_false (p : P) (not_p : ¬ P) : False :=
  not_p p

-- Example: To prove `¬ P` in term mode, we introduce `p : P` and produce a term of type `False`
theorem notP_term (h : P → False) : ¬ P :=
  fun p => h p

-- More examples: To prove `¬ P` in tactics mode, we introduce `p : P` and show `False`
theorem notP_tactics_1 (h : P → False) : ¬ P := by
  intro p
  exact h p

theorem notP_tactics_2 (h : P → False) : ¬ P := by
  intro p
  apply h at p
  exact p

theorem notP_tactics_3 (h : P → False) : ¬ P := by
  intro p
  apply h
  exact p

-- An example using `False.elim`
#check False.elim

example : P ∧ ¬P → Q :=
  fun ⟨p, np⟩ => -- Destructured argument of the conjunction `P ∧ ¬P`, we have `p : P` and `np : ¬ P`
    -- Recall that `¬ P` is defined as `P → False`, so applying `np` to `p` returns a term of type `False`
    let f : False := np p
    False.elim f

-- The same example without destructured arguments
example : P ∧ ¬P → Q :=
  fun p_np => -- Non-destructured argument of the conjunction `P ∧ ¬P`, we have `p_np : P ∧ ¬P`
    let f : False := p_np.2 p_np.1
    False.elim f

/--
Exercise 1.A.1:

Provide a proof for the transitivity of `→` in **term**-mode.
-/
theorem Q1A1 : (P → Q) ∧ (Q → R) → (P → R) := -- You are not allowed to use tactics (`by` keyword) in this task
  fun ⟨pq, qr⟩ p => qr (pq p)

/--
Exercise 1.A.2:

Provide a proof for the transitivity of `→` in **tactic**-mode.
You may only use the tactics `intro`, `apply`, and `exact`.
-/
theorem Q1A2 : (P → Q) ∧ (Q → R) → (P → R) := by
  intro ⟨pq, qr⟩ p 
  apply qr 
  apply pq 
  exact p

/--
Exercise 1.B.1:

Provide a proof for the contraposition in **term**-mode.
Hint: The examples above about negation and `False.elim` might be helpful.
-/
theorem Q1B1 : (P → Q) → (¬Q → ¬P) := -- You are not allowed to use tactics (`by` keyword) in this task
  fun pq nq p => nq (pq p)

/--
Exercise 1.B.2:

Provide a proof for the contraposition in **tactic**-mode.
You may only use the tactics `intro`, `apply`, `by_contra`, and `exact`.
-/
theorem Q1B2 : (P → Q) → (¬Q → ¬P) := by
  intro pq nq p
  apply nq 
  apply pq 
  exact p
