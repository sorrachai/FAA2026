/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-!

**Lean = Functional Programming Language + Interactive Proof Assistant**

We start by learning how to state and prove simple logical statements in Lean.

## Terms and types in Lean
In Lean, the basic expressions we work with are called `terms`.
Every well-typed term has a `type`.

If `x` is a term of type `T`, we write `x : T`.

We can think of a type as a collection of possible objects, and
a term of that type as one particular object in the collection.
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

-- TODO: write out (move to Sheet1')
#check n       -- n : ℕ
#check P1      -- P1 : Prop
#check (1 = 1) -- 1 = 1 : Prop
#check ℕ       -- ℕ : Type
#check Type    -- Type : Type 1

/-
Finally, a proof of a proposition is a term whose type is that proposition.
A term of type `1=1` is a valid proof of `1=1`
-/

def h : 1 = 1 := rfl
-- h is a proof term of `1 = 1`.
-- `rfl` is the reflexivity proof `a = a` for any object `a`.

-- This is valid Lean, but proofs are conventionally declared using `theorem`.

/-!
## How to state a theorem in Lean

theorem [name] (optional parameters/assumptions) : [proposition] := [proof]
-/

theorem one_eq_one : 1 = 1 := sorry
theorem one_eq_one' : P1 := sorry

-- `sorry` is a placeholder for a missing proof.
-- Lean allows the file to continue, but warns that the declaration uses `sorry`.

theorem one_neq_one : Q1 := sorry
-- `Q1` (1 ≠ 1) is false! So a theorem containing `sorry` should not be regarded as proven.

-- Let's check the type of one of these theorems
#check one_eq_one -- one_eq_one has type 1 = 1

/-!
In Lean, propositions are types and proofs are terms. To prove P : Prop means to construct a term h : P.
* P : Prop` means `P` is a (specific) proposition
* `h : P` means `h` is a proof of `P`.
* `theorem` tells Lean to treat every proof as a black-box.
-/


/-!
# How to prove a theorem in Lean
Under the hood, Lean verifies a proof by type-checking. Below are two simple examples.
The details how type-checking works are not our main focus in this course.
-/

theorem modus_ponens (P Q : Prop) (h_pq : P → Q) (h_p : P) : Q :=
  sorry

theorem conjunction (P Q : Prop) (h_p : P) (h_q : Q) : P ∧ Q :=
  sorry
  -- And.intro is a Lean (constructor) function of type P → Q → P ∧ Q.

/-!
## Using basic tactics
Tactics are the interactive way to write a proof in Lean.
Given a theorem statement, our objective is to tell Lean the proof by using basic tactics.
This is a game: we start with initial goal given by the theorem and provide a sequence of tactics to close the goal.
There are ∼ 20 tactics that will be often used. We will introduce new tactics as we go along.

* `rfl`   -- reflexive property a = a: the goal can be closed because two objects are definitionally equal
* `exact` -- the goal can be closed by exactly this hypothesis (i.e., because the goal is definitionally equal to it)
* `intro` -- reduce a goal of the form `P → Q` to `Q` and obtain `h : P` as a new hypothesis
          -- i.e., to prove implication, let's assume P and then we prove Q
* `constructor` -- break down the goals of the form P ∧ Q or P ↔ Q into subgoals
                -- i.e., to prove P ∧ Q, let's prove P     and Q     separately
                --       to prove P ↔ Q, let's prove P → Q and Q → P separately
-/

section
-- Throughout this sheet, `P`, `Q` denote propositions.
variable (P Q : Prop)

example : P = P := rfl
example : 2 + 1 + 1 = 4 := rfl

example : P → P := by
  sorry

example : P → (Q → P) := by
  sorry

example (hP: P) (hQ: Q) : P ∧ Q := by
  constructor
  · exact hP
  · exact hQ

example: P ∧ Q ↔ Q ∧ P:= by
  constructor
  · sorry
  · sorry
