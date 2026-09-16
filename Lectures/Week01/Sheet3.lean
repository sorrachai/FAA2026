import Mathlib.Tactic

/-!
### Function types

A function has an input type and an output type.
`A → B` is the type of functions that take an input of type `A` and return an output of type `B`.
-/
#check ℕ → ℤ                   -- the term `ℕ → ℤ` has type `Type`
#check fun (x : ℕ) ↦ (x : ℤ)   -- a function of type `ℕ → ℤ`

/-!
`A → B → C` is interpreted as `A → (B → C)`.

Such a function first takes an input of type `A` and returns a new
function of type `B → C`. That new function takes an input of type `B`
and returns an output of type `C`.

Supplying only the first argument is called partial application.
-/
def f : ℕ → ℕ → Prop :=
  fun x ↦
    fun y ↦
      x = y

#check f       -- f : ℕ → ℕ → Prop
#check f 0     -- f 0 : ℕ → Prop    (*partial application*)
#check f 0 0   -- f 0 0 : Prop


/-!
### New tactic `rewrite`

Suppose we have an equality `h : a = b`.
The tactic `rewrite [h]` replaces occurrences of `a` by `b`.

We can rewrite both in the goal and in a hypothesis.
* `rewrite [h]` replaces `a` by `b` in the goal.
* `rewrite [h] at hP` replaces `a` by `b` in the hypothesis `hP`.
* `rewrite [← h]` rewrites in the opposite direction, replacing `b` by `a`.

The tactic `rw` behaves like `rewrite` and then tries to close
the resulting goal using `rfl`.

**Example 1: rewrite using an equality**

Suppose the goal is `a + 1 = b + 1` and we have `h : a = b`.

* Tactic state **before** `rewrite [h]`:
  *Hypothesis*: `h : a = b`
  *Goal*: `⊢ a + 1 = b + 1`

* Tactic state **after** `rewrite [h]`:
  *Hypothesis*: `h : a = b`
  *New goal*: `⊢ b + 1 = b + 1`
-/
example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  rewrite [h]   -- replace a by b
  rfl           -- b+1 = b+1

example (a b : ℕ) (h : a = b) : a + 1 = b + 1 := by
  rewrite [← h] -- replace b by a
  rfl           -- a+1 = a+1

/-!
**Example 2: rewrite using a function definition**

We can also give `rewrite` the name of a definition. It then unfolds
that definition in the goal.

* Tactic state **before** `rewrite [f]`:
  *Goal*: `⊢ f 0 0`

* Tactic state **after** `rewrite [f]`:
  *New goal*: `⊢ 0 = 0`

The tactic `rw` closes this last goal automatically using `rfl`.
-/
example : f 0 0 := by -- Prove using `rewrite`
  sorry

example : f 0 0 := by -- Prove using `rw`
  sorry


/-! ### More new tactics
* `by_contra h`   -- assume the negation `h` of the goal and prove `False`
* `contradiction` -- we are done because we have contradicting hypotheses `hnp : ¬ P` and `hp : P`
* `trivial`       -- apply simple tactics such as `rfl`, `assumption`, or `contradiction`
-/

-- Prove by contradiction
example (a b : ℕ) (h1 : a = b) : a = b := by
  by_contra h2
  contradiction -- h2 : ¬(a = b), h1 : a = b
  -- alternatively, we can also tell Lean the contradicting hypotheses directly using `exact h2 h1`

theorem modus_tollens (P Q : Prop) (hPQ : P → Q) (hnQ : ¬ Q) : ¬ P := by
  sorry


/-!
* `symm`        -- transform a goal (or hypothesis) `x = a` to `a = x`
* `assumption`  -- there is a hypothesis `h` s.t. `exact h` can close the goal
-/

example (x : ℕ) : f 0 x → x = 0 := by
  sorry

-- Give a direct proof
example (x : ℕ) : f x 1 → x ≠ 2 := by sorry

example (x y : ℕ) : f 0 x ∧ f 0 y → x = y := by sorry
