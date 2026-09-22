/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card

/- This exercise covers the essential concepts from Week 2:
- Quantifiers: universal (∀) and existential (∃)
- Set theory basics: membership (∈), subset (⊆), union (∪), intersection (∩)
- New tactics: `intro`, `use`, `obtain`, `left`, `right`, `cases`, `by_cases`, `ext`, `rintro`
- Set operations and extensionality principles
-/

/-! ## Part 1: Quantifiers and Basic Logic

Working with universal (∀) and existential (∃) quantifiers.
Remember: `∀ x, P x` is the same as `(x : α) → P x` in Lean.
-/

section Quantifiers

-- Exercise 1: Basic universal quantifier
-- Hint: Use `intro` to assume an arbitrary element, then prove the property
example : ∀ n : ℕ, n + 0 = n := by
  sorry

-- Exercise 2: Basic existential quantifier
-- Hint: Use `use` to provide a witness that satisfies the property
example : ∃ n : ℕ, n + 3 = 7 := by
  sorry

-- Exercise 3: Multiple existentials
-- Hint: Provide witnesses for both variables using `use`
example : ∃ n m : ℕ, n + m = 5 := by
  sorry

-- Definition for even numbers
def IsEven (n : ℤ) : Prop := ∃ k, n = 2 * k

-- Exercise 4: Working with definitions
-- Hint: Use `obtain` to extract the witness and property from the existential
example (h : ∃ n : ℤ, IsEven n ∧ n > 10) : ∃ m : ℤ, m > 5 := by
  sorry

-- Exercise 5: Combining quantifiers with logic
-- Hint: Unfold the definition, obtain the witness, then provide a new witness
example (n : ℤ) (h : IsEven n) : IsEven (n + 2) := by
  sorry

end Quantifiers

/-! ## Part 2: Set Theory Fundamentals

Basic set operations and their properties.
Sets in Lean are functions α → Prop.
-/

section SetBasics

open Set
variable {α : Type*}
variable (A B C D : Set α)

-- Exercise 6: Reflexivity of subset
-- Hint: Rewrite using subset definition, then use `intro` and `assumption`
#check subset_def
example : A ⊆ A := by
  sorry

-- Exercise 7: Empty set is subset of everything
-- Hint: Use subset definition, then `exfalso` to derive contradiction from empty set membership
example : ∅ ⊆ A := by
  sorry

-- Exercise 8: Transitivity of subset
-- Hint: Use subset definition, then chain the implications
example : A ⊆ B → B ⊆ C → A ⊆ C := by
  sorry

-- Exercise 9: Intersection subset
-- Hint: Use subset and intersection definitions
example : A ∩ B ⊆ B := by
  sorry

-- Exercise 10: Subset intersection characterization
-- Hint: Use constructor to split the conjunction, then prove each direction
example : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := by
  sorry

end SetBasics

/-! ## Part 3: Disjunctions and Case Analysis

Working with logical OR (∨) and case analysis.
-/

section Disjunctions

open Set
variable {α : Type*}
variable (A B C : Set α)

-- Exercise 11: Left inclusion in union
-- Hint: Use `left` to choose the first disjunct
example : A ⊆ A ∪ B := by
  sorry

-- Exercise 12: Case analysis with excluded middle
-- Hint: `by_cases` splits into two cases automatically
example (x : α) : x ∈ A ∨ x ∉ A := by
  sorry

-- Exercise 13: Union subset characterization
-- Hint: Use constructor for the biconditional, then `cases` to handle the union
#check mem_union
lemma union_subset_iff : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  sorry

-- Exercise 14: Using the characterization
-- Hint: Apply the lemma you just proved
example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A := by
  sorry

end Disjunctions
