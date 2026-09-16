import Mathlib.Tactic

/-! ### New tactic `apply`
    -- Suppose we have a hypothesis `h : P → Q` (from the current assumptions or from a library)
    -- We can apply `h : P → Q`
       -- on a hypothesis of type `P` to move the hypothesis **forward** to `Q`
       -- on a goal `Q` to push the goal **backward** to `P`.

    **Forward: transform an assumption**
    -- If we have `hp : P`, then `apply h at hp` transforms `hp` into `hp : Q`

       * Tactic state **before** `apply h at hp`:
         *Target hypothesis*: `hp : P`
         *Goal*: `⊢ ...`

       * Tactic state **after** `apply h at hp`:
         *New target hypothesis*: `hp : Q`
         *Goal*: `⊢ ...` (same as before)

    **Backward: transform the goal**
    -- If the goal is in the form `Q`, then `apply h` changes the goal to `P`

       * Tactic state **before** `apply h`:
         *Goal*: `⊢ Q`

       * Tactic state **after** `apply h`:
         *New goal*: `⊢ P`
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

-- To keep `h2 : P`, we can also define a new local proof instead of transforming `h2`
example (h : P → Q) (h2 : P) : Q := by
  let h2' : Q := h h2 -- A new local proof `h2' : Q`, we still have the old `h2 : P`
  -- We can also use `have` instead of `let`
  exact h2'

-- Example 2a: Using apply to transform the goal
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  -- **Backward**: apply hypothesis at the goal (`apply` without at)
  apply h2 -- reduce goal to Q
  apply h1 -- reduce goal to P
  exact h3 -- close with h3

-- Example 2a': Using apply with function composition to transform the goal
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  -- **Backward**: apply hypothesis at the goal (`apply` without at)
  let f : P → R := h2 ∘ h1
  apply f
  exact h3

-- Example 2b: Using apply with existing assumptions
example (h1 : P → Q) (h2 : Q → R) (h3 : P) : R := by
  -- **Forward**: apply hypothesis at another hypothesis (`apply at` ...)
  apply h1 at h3
  apply h2 at h3
  exact h3


/-!
## `apply` is flexible
The apply tactic in Lean can be used not only to transform goals but also to produce subgoals when the hypothesis you are applying has multiple premises.
This is often the case when you have implications or functions that require more than one argument.
-/
example {S : Prop} (h0 : P ∧ Q ∧ R) (h : P → Q → R → S) : S := by
  apply h -- three subgoals `P`, `Q`, `R`
  · -- subgoal `P`
    exact h0.left
  · -- subgoal `Q`
    exact h0.right.left
  · -- subgoal `R`
    exact h0.right.right

#check lt_trans -- lt_trans (...) : a < b → b < c → a < c
example (x y z : ℝ) (hab : x < y) (hbc : y < z) : x < z := by
  apply lt_trans (b := y)
  · -- subgoal `x < y`
    exact hab
  · -- subgoal `y < z`
    exact hbc
