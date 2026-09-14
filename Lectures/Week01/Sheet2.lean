import Mathlib.Tactic

/-! New tactics
  * `apply` -- Suppose we have `h: P → Q`, which can be from the current assumptions or from the library.
            -- we apply `h` on hypothesis to move assumptions forward and apply on goal to push the goal backward.
  * If we have `hp : P`, then `apply h at hp` yields a new assumption `Q`
  * If the goal is in the form `Q`, then `apply h` changes the goal to `P`
-/

variable (P Q R : Prop)

-- Example 1a: Using apply to transform the goal
lemma piq (h : P → Q) (h2 : P) : Q := by
  apply h
  exact h2

-- Example 1b: Using apply with existing assumptions
example (h : P → Q) (h2 : P) : Q := by
  apply h at h2
  trivial

-- Example 2a: Using apply to transform the goal
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  sorry

-- Example 2b: Using apply with existing assumptions
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  sorry

/-!
## `apply` is flexible
The apply tactic in Lean can be used not only to transform goals but also to produce subgoals when the hypothesis you are applying has multiple premises.
This is often the case when you have implications or functions that require more than one argument.
-/
example {S : Prop} (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by sorry

example {S} : P → Q → R → S ↔ ((P ∧ Q ∧ R) → S) := by tauto

/-!
## More examples
-/
#check lt_trans
example (x y z : ℝ) (hab : x < y) (hbc : y < z) : x < z := by
  apply lt_trans
  all_goals sorry

example (a b c : ℝ) (hab : a < b) (hbc : b < c) : a < c := by
  trans b
  · exact hab
  · exact hbc
