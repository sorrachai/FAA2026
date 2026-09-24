/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-
So far we have seen the following tactics:
- `intro` - introduce hypotheses for implications
- `exact` - provide exact proof terms
- `constructor` - split conjunctions and biconditionals
- `apply` - use implications and functions backwards
- `rw` / `rewrite` - rewrite using equalities
- `unfold` - expand definitions
- `use` - provide witnesses for existentials
- `obtain` - extract components from conjunctions
-/


-- In this week, we will learn more tactics that allows us to prove basic set theory statement.

/-! Set theory

In Lean, a set is always a set of objects of some type.
* If α is a type, then the type Set α consists of sets of elements of α
* For example, the type Set ℕ consists of sets of natural numbers.
  Given n : ℕ and s : Set ℕ, the expression n ∈ s means n is a member of s
* Two special sets for Set α: ∅ and univ: ∅ is the set having zero elements from α
  and univ is the set of all elements from α

Basic set operations are built-in.
* s ⊆ t ↔ ∀ x ∈ s, x ∈ t
* s ∪ t ↔ ∀ x, x ∈ s ∨ x ∈ t
* s ∩ t ↔ ∀ x, x ∈ s ∧ x ∈ t
-/

#check Set.subset_def
#check Set.union_def
#check Set.inter_def

open Set
def S1 : Set (ℕ) := {10}
def S2 : Set (ℕ) := {10,20}


#check S1
#check 10 ∈ S1
#check S1 ⊆ S2

#check mem_singleton_iff
example : S1 ⊆ S2 := by
  rw [S1,S2]
  rw [subset_def]
  intro x hx
  rw [mem_insert_iff]
  rw [mem_singleton_iff] at hx
  left
  assumption

/-! For technical details
 (1) def Set (α : Type u) := α → Prop.
     So a set of elements of type α is just a boolean function α → Prop
     saying whether an element belongs.
 (2) Membership is defined as:
     def Set.Mem (x : α) (s : Set α) : Prop := s x
     So x ∈ s is syntactic sugar for s x
-/
example : (10 ∈ S1) = (S1 10) := by rfl

--  (3) How to define an emptyset?
def my_emptyset : Set ℕ := fun _ ↦ False
example: my_emptyset = ∅  := rfl

--  (4) How to define a universe set?
def my_univ : Set ℕ := fun _ ↦ True
example: my_univ = univ := rfl


variable {α : Type*}
variable (A B C D : Set α)

example : A ⊆ A := by
  rw [subset_def]
  intros
  assumption

example : A ⊆ A := by rfl

example : ∅ ⊆ A := by
  rw [subset_def]
  intros
  contradiction

-- running examples
#check mem_inter_iff
#check subset_def
example : A ∩ B ⊆ B := by
  rw [subset_def]
  intro x h
  rw [mem_inter_iff] at h
  obtain ⟨ha,hb⟩ := h
  assumption

-- Exercise 1: resolve the sorry
#check subset_def
example : A ⊆ B → B ⊆ C → A ⊆ C := by
-- Gokul Rajiv
  -- repeat rw [subset_def]
  -- intro HAB HBC x HA
  -- exact HBC x (HAB x HA)
-- Sorrachai
  intro h1 h2
  rw [subset_def]
  rw [subset_def] at h1
  rw [subset_def] at h2
  intro x h
  apply h2
  apply h1
  assumption

-- Sebastian Thomas - Wednesday, 23 September 2026, 3:01 PM
--Forward Apply:
example : A ⊆ B → B ⊆ C → A ⊆ C := by
  intro h_ab h_bc
  rw [subset_def]
  rw [subset_def] at h_ab
  rw [subset_def] at h_bc
  intro x h
  apply h_ab at h
  apply h_bc at h
  assumption
--```

-- Exercise 2:  More exercises
#check Set.inter_def
example : A ∩ B ⊆ B := by
  rw [subset_def, inter_def]
  intro x h
  rw [sep_mem_eq, mem_inter_iff] at h
  cases h
  assumption

example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
  intro a b
  rw [subset_inter_iff]
  exact ⟨a, b⟩
