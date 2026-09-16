import Mathlib.Tactic



section BasicLogic

/-! ## Basic Logic

These exercises practice the fundamental logical reasoning tactics.
Remember:
- Use `intro` to introduce hypotheses for implications
- Use `exact` when you have exactly what you need
- Use `constructor` to split goals like `P ∧ Q` or `P ↔ Q`
-/

variable (P Q R : Prop)

-- Example: reflexivity of implication
example : P → P := by
  intro h
  exact h

-- Exercise 3: Simple implication chain
example : P → (Q → P) := by
  sorry

-- Exercise 4: Transitivity of implication
example : (P → Q) → (Q → R) → (P → R) := by
  sorry

-- Exercise 5: Conjunction introduction
example (hP : P) (hQ : Q) : P ∧ Q := by
  sorry

-- Exercise 6: Conjunction commutativity
example : P ∧ Q ↔ Q ∧ P := sorry

-- Exercise 7: More complex logical reasoning
example : (P → Q) ∧ (P → R) → (P → Q ∧ R) := by
  sorry

end BasicLogic


section ApplyTactic

variable (P Q R S : Prop)

-- Example: basic apply usage
example (h1 : P → Q) (h2 : P) : Q := by sorry

-- Exercise 8: Chaining apply
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by sorry

-- Exercise 9: Apply with multiple premises (from w1sheet2 style)
example (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by sorry

-- Exercise 10: Mixed apply and intro
example : (P → Q) → (Q → R) → (P → R) := by sorry

end ApplyTactic

section Functions

def f : (ℕ → ℕ → Prop) := fun x : ℕ ↦ fun y : ℕ ↦ x = y

-- Exercise 11: Basic function application
example : f 0 0 := by sorry

-- Exercise 12: Function reasoning
example (x : ℕ) : f 0 x → x = 0 := by sorry

-- Exercise 13: Function with inequality
example (x : ℕ) : f x 1 → x ≠ 2 := by sorry

-- Exercise 14: More complex function reasoning
example (x y : ℕ) : f 0 x ∧ f 0 y → x = y := by sorry

end Functions


section Challenge
/-
Many propositions cannot be proven in intuitionistic logic
and require the law of the excluded middle (or something equivalent).
-/
#check Classical.em

/--
The exercise below is a **challenge** exercise.
It requires concepts outside the material we have
covered and we do not expect you to solve it.

We provide some examples that might be helpful.
-/
example : ¬¬P → P := -- term mode
  match Classical.em P with
  | Or.inl p => (fun _ => p)
  | Or.inr np => (fun nnp => False.elim (nnp np))

example : ¬¬P → P := by -- tactics mode
  cases Classical.em P with
  | inl p =>
    intro _
    exact p
  | inr np =>
    intro nnp
    contradiction

-- Example: pattern matching on Or and using `left` / `right`
example : (P ∨ (Q ∧ R)) → (R ∧ Q) ∨ P := by
  intro p_or_qr
  cases p_or_qr with
  -- if p_or_qr is constructed from Or.inl, we get `p : P`
  | inl p =>
    right -- we prove the right part of the disjunction `(R ∧ Q) ∨ P`
    exact p
  -- if p_or_qr is constructed from Or.inr, we get `qr : Q ∧ R`
  | inr qr =>
    left -- we prove the left part of the disjunction `(R ∧ Q) ∨ P`
    constructor
    · exact qr.2
    · exact qr.1

/--
Exercise 15:

Prove the following proposition.
You may only use the tactics `constructor`, `cases`, `contradiction`,
  `left`, `right`, `intro`, `apply`, and `exact`.

Hint: Use a case distinction on `Classical.em P`.
-/
example {P Q R : Prop} : (P → Q ∨ R) ↔ ((P → Q) ∨ (P → R)) := by
  sorry

end Challenge
