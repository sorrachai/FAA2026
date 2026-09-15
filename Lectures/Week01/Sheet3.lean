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
#check f 0     -- f 0 : ℕ → Prop    (_partial application_)
#check f 0 0   -- f 0 0 : Prop


/- ### New tactics
* `rewrite` [h] -- replace a term in the goal with an equivalent term [h].
* `rw`          -- rewrite, followed by trying to close the goal by rfl.
* `symm`        -- transform a goal (or hypothesis) `x = a` to `a = x`
* `assumption`  -- there is a hypothesis `h` s.t. `exact h` can close the goal
-/

example : f 0 0 := by
  rewrite [f]
  rfl

example : f 0 0 := by
  rw [f]

example (x : ℕ) : f 0 x → x = 0 := by
  sorry

-- Give a direct proof
example (x : ℕ) : f x 1 → x ≠ 2 := by sorry

example (x y : ℕ) : f 0 x ∧ f 0 y → x = y := by sorry


/-! Bonus:
* `by_contra`     -- assume the negation of the goal and prove `False`
* `contradiction` -- we are done because we have a proof of `h' : ¬ P` and `h : P`
* `trivial`       -- apply `rfl` or `assumption` or `contradiction` tactics
-/

-- Prove by contradiction
example (h1 : a = b) : a = b:= by sorry

example (x : ℕ) : f x 1 → x ≠ 2 := by sorry
