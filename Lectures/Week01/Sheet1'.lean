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

-- Type ℕ, ℚ, ℝ using \N, \Q, \R
def n : ℕ := 100   -- n is a term of type ℕ, defined to be 100
def z : ℚ := -0.1  -- z is a term of type ℚ
def r : ℝ := 42.42 -- r is a term of type ℝ

/-
We can check the type of a term using `#check`
-/
#check n -- n : ℕ
#check z -- z : ℚ
#check r -- r : ℝ

/-
Types can themselves be terms. For example, ℕ is a term of type `Type`.
-/
def t : Type := ℕ

#check t -- t : Type
#check ℕ -- ℕ : Type

/-
Propositions are also terms: they have type `Prop`.
-/
def P1 : Prop := 1 = 1   -- P1 is the proposition `1 = 1`
def Q1 : Prop := 1 ≠ 1   -- Q1 is the proposition `1 ≠ 1`

#check P1      -- P1 : Prop

example (hP : P) : P :=
  by exact hP

/-!
## How to state a theorem in Lean

theorem [name] (optional parameters/assumptions) : [proposition] := [proof]

You can also use the keyword `lemma` instead of `theorem`.

We will sometimes also use the keyword `example`, which you can think of like a theorem without a name.
-/

theorem one_eq_one : 1 = 1 :=
  rfl

-- `rfl` is the reflexivity proof `a = a` for any `a`.
#check rfl -- rfl (...) : a = a

#check one_eq_one -- one_eq_one : 1 = 1

theorem one_eq_one' : P1 := sorry
-- `sorry` is a placeholder for a missing proof.
-- Lean allows the file to continue, but warns that the declaration uses `sorry`.

theorem fake_theorem : 1 ≠ 1 := sorry

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

-- Reminder: theorem [name] (optional parameters/assumptions) : [proposition] := [proof]

theorem modus_ponens (P Q : Prop) (h_pq : P → Q) (h_p : P) : Q :=
  -- h_pq has function type `P → Q` (input `P`, output `Q`)
  -- h_p has type `P`
  -- We want to obtain a term of type `Q`
  h_pq h_p
  -- Applying the function h_pq (type `P → Q`) to h_p (type `P`)
  -- returns a term of type `Q`

theorem conjunction (P Q : Prop) (h_p : P) (h_q : Q) : P ∧ Q :=
  -- `And.intro` is a Lean (constructor) function of type `A → (B → A ∧ B)`.
  And.intro h_p h_q
  -- Applying And.intro to h_p (type `P`) and then h_q (type `Q`)
  -- returns a term of type `P ∧ Q`

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

/-!
Reminder: theorem [name] (optional parameters/assumptions) : [proposition] := [proof]
-/

/-! ### rfl
* `rfl`         -- reflexive property a = a: the goal `a = a` can be closed because two objects are definitionally equal
-/
example : P = P := rfl -- already seen

example : P = P := by
  rfl

example : 4 = 4 := by
  rfl


/-! ### exact
* `exact t` -- close a goal `P` by providing a term `t : P`.
               The term can be a hypothesis or a proof obtained by applying a theorem or function.
-/

example (hP : P) : P := by
  exact hP

example (hP : P) (hQ : Q) : Q := by
  exact hQ

#check Eq.symm -- Eq.symm ... (h : a = b) : b = a

example (a b : ℕ) (h : a = b) : b = a := by
  exact (Eq.symm h)


/-! ### intro
* Setting: Goal of the form `P → Q`
* `intro h`     -- to prove a goal of the form `P → Q`,
                   we introduce a new hypothesis `h : P` and change the goal to `Q`
                -- i.e., to prove an implication, we assume P and then prove Q

* Tactic state **before** `intro h`:
  *Goal*: `⊢ P → Q`

* Tactic state **after** `intro hP`:
  *New hypothesis*: `hP : P`
  *New goal* : `⊢ Q`
-/
example (hQ : Q) : P → Q := by
  intro hP
  exact hQ

example : P → P := by
  intro h
  exact h

example : P → (Q → P) := by
  intro p
  intro q
  exact p


/- ### constructor
* `constructor` -- break down the goals of the form `P ∧ Q` or `P ↔ Q` into subgoals
                -- i.e., to prove `P ∧ Q`, let's prove `P`     and `Q`     separately
                --       to prove `P ↔ Q`, let's prove `P → Q` and `Q → P` separately
-/
example (hP : P) (hQ : Q) : P ∧ Q := by
  constructor
  · -- subgoal P, type \dot or \. to write "·"
    exact hP
  · -- subgoal Q
    exact hQ

/-
Destructuring terms of type `P ∧ Q`
-/
example : (P ∧ Q) → P := by
  intro h
  exact h.left -- also possible: exact h.1

example : (P ∧ Q) → P := by
  intro ⟨hP, hQ⟩ -- type `\<` and `\>` to write `⟨` and `⟩`
  exact hP


example (R S : Prop) : (P ∧ Q ∧ R ∧ S) → R := by
  intro h
  exact h.right.right.left
  -- also possible: exact h.2.2.1

example (R S : Prop) : (P ∧ Q ∧ R ∧ S) → R := by
  intro ⟨hP, hQ, hR, hS⟩ -- or: intro ⟨hP, ⟨hQ, ⟨hR, hS⟩⟩⟩
  exact hR


example : (P ∧ Q) → Q := by
  intro h
  exact h.right

example : (P ∧ Q) → Q := by
  intro ⟨hP, hQ⟩
  exact hQ


example : P ∧ Q ↔ Q ∧ P:= by
  constructor
  · -- Subgoal 1: P ∧ Q → Q ∧ P
    intro ⟨hP, hQ⟩
    constructor
    · exact hQ
    · exact hP
  · -- Subgoal 2: Q ∧ P → P ∧ Q
    intro ⟨hQ, hP⟩
    constructor
    · exact hP
    · exact hQ
