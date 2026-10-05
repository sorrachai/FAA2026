/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivier Fischer, Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false

/-! ## Lists in Lean
  In the previous sheet we defined our own `List` type. We now
  use Lean's built-in `List`, which has the same structure.

  Lean defines the notation `[]` for `nil` and `::` for `cons`.
-/

example : [1,2,3] = 1 :: 2 :: 3 :: [] := by rfl

-- Let's again define a custom append function
def append {α : Type} (xs : List α) (ys : List α) : List α :=
  match xs with
  | [] => ys
  | a :: as => a :: (append as ys)

#check append
#eval append [1, 2, 3] [4, 5, 6]

/-
Our `append` has the same behavior as `List.append`. From now on, we use
Mathlib’s built-in version, written `++`.
-/
#eval List.append [1, 2, 3] [4, 5, 6]
#eval [1,2,3] ++ [4,5,6]


-- Compute the length of a list
def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

#check List.nil_append
#check List.cons_append

-- ## Induction over lists
theorem len_append_induction {α : Type} (x : α) (l : List α) : len (l ++ [x]) = 1 + len l  := by
  induction l with
  | nil =>
    -- Base case: prove the claim for empty list []
    rw [List.nil_append]
    unfold len
    unfold len
    rfl
    -- one-line proof: simp [len]
  | cons y ys tail_ih =>
    -- Induction step `l = y :: ys`, `y : α`, `ys : List α`
    -- Hypothesis `tail_ih`: claim holds for tail `ys`
    -- Goal: show that the claim holds for `y :: ys`
    rw [List.cons_append]
    unfold len
    rw [tail_ih]
    -- one-line proof: simp [len, tail_ih]

-- Alternative proof by recursion
theorem len_append' {α : Type} (x : α) (l : List α) : len (l ++ [x]) = 1 + len l  := by
  match l with
  | []  => rfl
  | y :: ys =>
    simp only [List.cons_append,len]
    simp only [Nat.add_left_cancel_iff]
    apply len_append' -- recursive call on the structurally smaller list `ys`

-- Another proof by recursion using cases instead of pattern matching
theorem len_append_cases {α : Type} (x : α) (l : List α) : len (l ++ [x]) = 1 + len l  := by
  cases l <;> expose_names
  · unfold len
    rw [List.nil_append, add_zero, Nat.add_eq_left]
    rewrite [len]
    rfl
    -- Another option:
    -- simp [len]
  · simp only [List.cons_append, len]
    simp only [Nat.add_left_cancel_iff]
    apply len_append_cases x tail -- recursive call


/- ## Simplification with `simp`

The `simp` tactic performs routine rewriting and computation using Lean's
collection of simplification lemmas. For example, it can simplify arithmetic,
list operations, and functions applied to known constructors.

* `simp` uses Lean's standard simplification lemmas.
* `simp [f, h]` additionally uses the definition `f` and the lemma or hypothesis `h`.
* `simp only [f, h]` uses only the listed definitions and lemmas
* `simp?` tries `simp` and suggests an explicit `simp only [...]` proof in
          the InfoView. Replace `simp?` with this suggestion in the final proof.
-/
example (xs : List ℕ) : [] ++ xs = xs := by
  simp

example (x : ℕ) (xs : List ℕ) : len (x :: xs) = 1 + len xs := by
  simp [len]

example (m n : ℕ) (h : m = n) : m + 0 = n := by
  simp [h]

example (n : ℕ) : 0 + n + 0 = n := by
  simp only [Nat.zero_add, Nat.add_zero]

-- `simp?` displays a suggested `simp only [...]` proof in the InfoView.
example (n : ℕ) : n * 1 = n := by
  simp? -- Suggested replacement: `simp only [mul_one]`


-- ## Induction over binary trees
-- In the previous sheet we defined our own binary tree type. We
-- now use Mathlib's BinaryTree, which has the same structure.

def mirror {α : Type} : (BinaryTree α) → BinaryTree α
  | .nil   => .nil
  | .node val left right => .node val (mirror right) (mirror left)


-- **Exercise 8**
-- Complete the induction proof on the mirror function
theorem mirror_mirror {α : Type} (t : BinaryTree α) :
    mirror (mirror t) = t := by
  induction t with
  | nil =>

    -- Option 1: using rewrite
    rewrite [mirror]
    rewrite [mirror]
    rfl

    -- Option 2: using unfold
    -- unfold mirror
    -- unfold mirror
    -- rfl

    -- Option 3: using simp (only)
    -- simp only [mirror]

  | node val left right ih_left ih_right =>
    simp only [mirror, ih_left, ih_right]


-- **Exercise 9**
-- (a) Complete the definition of my_map.
--     If the input list is [a1, a2, a3, ...],
--     the output list should be [f a1, f a2, f a3, ...]
def my_map {α β : Type} (f : α → β) : List α → List β
| [] => []
| a :: as => (f a) :: my_map f as

-- You can test your my_map function by replacing sorry by rfl
example : my_map (fun x => x + 1) [1, 2, 3] = [2,3,4] := rfl
example : my_map (fun s => s.length) ["hello", "a", "world"] = [5,1,5] := rfl

#check Function.comp_apply

-- (b) Complete the theorem below on map composition
theorem map_map_comp {α β γ : Type} (f : α → β) (g : β → γ) (l : List α) :
  my_map (g ∘ f) l = my_map g (my_map f l) := by
  induction l with
  | nil =>
    unfold my_map
    rfl
  | cons x xs tail_ih =>
    -- one-line proof: simp [my_map, tail_ih]
    unfold my_map
    rw [tail_ih]
    -- Note: `rfl` can already close the goal here, but we show the rewrites
    -- that can be applied to the goal to make the two sides match
    rewrite [Function.comp_apply]
    rewrite [my_map]
    rfl


-- **Exercise 10**
-- (a) Complete the definition of `my_filter`. The filter should remove all elements
--     that do not satisfy `p`. Hint: use the syntax `if ... then ... else ...`.
def my_filter {α : Type} (p : α → Bool) : List α → List α
| [] => []
| a :: as => if p a then a :: (my_filter p as) else (my_filter p as)

-- You can test your my_filter function by replacing sorry by rfl
example : my_filter (fun x => x % 2 == 0) [1, 2, 3, 4, 5, 6] = [2,4,6] := by rfl
example : my_filter (fun x => x > 42) [1, 2, 3, 4, 5, 6, 7] = [] := by rfl

-- (b) Prove the following theorem
theorem filter_append {α : Type} (p : α → Bool) (l1 l2 : List α) :
  my_filter p (l1 ++ l2) = (my_filter p l1) ++ (my_filter p l2) := by
  induction l1 with
  | nil =>
      simp [my_filter]
  | cons x xs tail_ih =>
      -- one-line proof: by_cases hx : p x <;> simp [my_filter, hx, tail_ih]
      simp [my_filter]
      by_cases hx : p x
      · simp [hx, tail_ih]
      · simp [hx, tail_ih]
