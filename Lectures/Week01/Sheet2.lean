import Mathlib.Tactic

/-! ### New tactic `apply`
    -- Suppose we have a hypothesis `h : P → Q` (from the current assumptions or from a library)
    -- We can apply `h : P → Q`
       -- on a hypothesis of type `P` to move the hypothesis **forward** to `Q`
       -- on a goal `Q` to push the goal **backward** to `P`.
    **Forward: transform an assumption**
    -- If we have `hp : P`, then `apply h at hp` yields a new assumption `hp : Q`
    **Backward: transform the goal**
    -- If the goal is in the form `Q`, then `apply h` changes the goal to `P`
-/

variable (P Q R : Prop)

-- Example 1a: Using apply to transform the goal
lemma piq (h : P → Q) (h2 : P) : Q := by
  apply h  -- **Backward**: apply hypothesis `h` at the goal
  exact h2

-- Example 1b: Using apply with existing assumptions
example (h : P → Q) (h2 : P) : Q := by
  apply h at h2 -- **Forward**: apply hypothesis `h` at hypothesis `h2`
  exact h2

-- Example 2a: Using apply to transform the goal
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  -- **Backward**: apply hypothesis at the goal
  sorry

-- Example 2b: Using apply with existing assumptions
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  -- **Forward**: apply hypothesis at another hypothesis
  sorry

/-!
## `apply` is flexible
The apply tactic in Lean can be used not only to transform goals but also to produce subgoals when the hypothesis you are applying has multiple premises.
This is often the case when you have implications or functions that require more than one argument.
-/
example {S : Prop} (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by
  apply h -- three subgoals `P`, `Q`, `R`
  · -- subgoal `P`
    sorry
  · -- subgoal `Q`
    sorry
  · -- subgoal `R`
    sorry

/-!
## More examples
-/
#check lt_trans -- lt_trans (...) : a < b → b < c → a < c
example (x y z : ℝ) (hab : x < y) (hbc : y < z) : x < z := by
  apply lt_trans (b := y)
  · -- subgoal `x < y`
    sorry
  · -- subgoal `y < z`
    sorry

example (a b c : ℝ) (hab : a < b) (hbc : b < c) : a < c := by
  trans b
  · -- subgoal `a < b`
    sorry
  · -- subgoal `b < c`
    sorry
