/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai, Olivier Fischer
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!

**Lean = Functional Programming Language + Interactive Proof Assistant**

We start by learning how to state and prove simple logical statements in Lean.

## Terms and types in Lean
In Lean, the basic expressions we work with are called `terms`.
Every well-typed term has a `type`.

If `x` is a term of type `T`, we write `x : T`.
-/

def n : ℕ := 100   -- n is a term of type ℕ, defined to be 100
def z : ℚ := -0.1  -- z is a term of type ℚ

/-
Types can themselves be terms. For example, ℕ is a term of type `Type`.
-/
def t : Type := ℕ

/-
Propositions are also terms: they have type `Prop`.
-/
def P1 : Prop := 1 = 1   -- P1 is the proposition `1 = 1`
def Q1 : Prop := 1 ≠ 1   -- Q1 is the proposition `1 ≠ 1`

/-
We can check the type of a term using `#check`
-/
#check n       -- n : ℕ
#check P1      -- P1 : Prop


/-!
## How to state a theorem in Lean

theorem [name] (optional parameters/assumptions) : [proposition] := [proof]
-/

theorem one_eq_one : 1 = 1 := rfl
-- `rfl` is the reflexivity proof `a = a` for any `a`.
#check rfl -- rfl (...) : a = a

theorem one_eq_one' : P1 := sorry
-- `sorry` is a placeholder for a missing proof.
-- Lean allows the file to continue, but warns that the declaration uses `sorry`.

-- Let's check the type of one of these theorems
#check one_eq_one -- one_eq_one has type 1 = 1

/-!
In Lean, propositions are types and proofs are terms.
To prove `P : Prop` means to construct a term `h : P`.
* `P : Prop` means `P` is a (specific) proposition
* `h : P` means `h` is a proof of `P`.
* `theorem` tells Lean to treat every proof as a black-box.
-/


/-!
# How to prove a theorem in Lean
Under the hood, Lean verifies a proof by type-checking. Below are two examples.
The details of how type-checking works are not our main focus in this course.
-/

theorem modus_ponens (P Q : Prop) (h_pq : P → Q) (h_p : P) : Q :=
  -- h_pq has function type `P → Q` (input `P`, output `Q`)
  -- h_p has type `P`
  -- We want to obtain a term of type `Q`
  sorry

theorem conjunction (P Q : Prop) (h_p : P) (h_q : Q) : P ∧ Q :=
  -- `And.intro` is a Lean (constructor) function of type `P → Q → P ∧ Q`.
  sorry

#check And.intro

/-!
## Using basic tactics
Tactics are the *interactive* way to write a proof in Lean.

Given a theorem statement, our objective is to tell Lean the proof by using basic tactics.
This is a game: we start with initial goal given by the theorem and provide a sequence of tactics to close the goal.
There are ∼20 tactics that will be often used. We will introduce new tactics as we go along.

* `rfl`         -- reflexive property a = a: the goal `a = a` can be closed because two objects are definitionally equal
* `exact t`     -- close the goal `P` by providing a term `t : P` (a hypothesis or a theorem/function)
* `intro h`     -- to prove a goal of the form `P → Q`, we introduce a new hypothesis `h : P` and change the goal to `Q`
                -- i.e., to prove an implication, we assume P and then prove Q
* `constructor` -- break down the goals of the form P ∧ Q or P ↔ Q into subgoals
                -- i.e., to prove P ∧ Q, let's prove P     and Q     separately
                --       to prove P ↔ Q, let's prove P → Q and Q → P separately
-/

section

variable (P Q : Prop) -- Throughout this sheet, `P`, `Q` denote propositions.

/-! Reminder: how to state a theorem in Lean
theorem [name] (optional parameters/assumptions) : [proposition] := [proof]
-/

/-! ### rfl
* `rfl`         -- reflexive property a = a: the goal `a = a` can be closed because two objects are definitionally equal
-/
example : P = P := by
  sorry

example : 4 = 4 := by
  sorry


/-! ### exact
* `exact t` -- close a goal `P` by providing a term `t : P`.
               The term can be a hypothesis or a proof obtained by applying a theorem or function.
-/
example (hP : P) : P := by
  sorry

example (hP : P) (hQ : Q) : Q := by
  sorry

#check Eq.symm -- Eq.symm ... (h : a = b) : b = a

example (a b : ℕ) (h : a = b) : b = a := by
  exact (Eq.symm h)


/-! ### intro
* `intro h`     -- to prove a goal of the form `P → Q`, we introduce a new hypothesis `h : P` and change the goal to `Q`
                -- i.e., to prove an implication, we assume P and then prove Q

* Tactic state **before** `intro h`:
  *Goal*: `⊢ P → Q`

* Tactic state **after** `intro h`:
  *New hypothesis*: `h : P`
  *New goal* : `⊢ Q`
-/
example (hQ : Q) : P → Q := by
  sorry

example : P → P := by
  sorry

example : P → (Q → P) := by
  sorry


/- ### constructor
* `constructor` -- break down the goals of the form P ∧ Q or P ↔ Q into subgoals
                -- i.e., to prove P ∧ Q, let's prove P     and Q     separately
                --       to prove P ↔ Q, let's prove P → Q and Q → P separately
-/
example (hP : P) (hQ : Q) : P ∧ Q := by
  sorry

/-
Destructuring terms of type `P ∧ Q`
-/
example : (P ∧ Q) → P := by
  intro h
  exact h.left -- or: h.1

example : (P ∧ Q) → P := by
  intro ⟨hP, hQ⟩ -- type `\<` and `\>` to write `⟨` and `⟩`
  exact hP

example : (P ∧ Q) → Q := by
  intro h
  sorry

example : (P ∧ Q) → Q := by
  intro ⟨hP, hQ⟩
  sorry


example: P ∧ Q ↔ Q ∧ P:= by
  constructor
  · -- Subgoal 1: P ∧ Q → Q ∧ P
    sorry
  · -- Subgoal 2: Q ∧ P → P ∧ Q
    sorry
