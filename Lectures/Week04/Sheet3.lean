/-
Copyright (c) 2025 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

set_option autoImplicit false
set_option tactic.hygienic false


/-
# Function Induction
So far, we have seen induction over ℕ. This week we will cover functional induction.
The core idea is that if a function is recursively defined, then
  you can prove it recursively as long as you show termination.
On the other hand,
  functional induction formalizes recursive proofs and
  tells you exactly what is needed to complete the proof.
These two proofs are equivalent, but
they may give you different perspective to think about a problem.
-/

-- functional induction
-- Pascal sum

def factorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

notation:10000 n "!" => factorial n

-- We can prove this fact by induction on Nat
lemma fact (n : ℕ) : 1 ≤ n ! := by
  induction n with
  | zero => simp [factorial]
  | succ n ih =>
    unfold factorial
    grw [← ih]
    simp only [mul_one, le_add_iff_nonneg_left, zero_le]

def P : ℕ → ℕ → ℕ
  | _, 0 => 1
  | 0, _ + 1 => 1
  | a + 1, b + 1 => P (a + 1) b + P a (b + 1)

-- In Lean, every recursively defined function is equipped with functional induction
#check P.induct
#check P.induct_unfolding

#eval                                 [P 0 0]
#eval                          [P 0 1,P 1 0]
#eval                  [P 2 0,P 1 1, P 2 0]
#eval         [P 3 0,P 2 1, P 1 2, P 0 3]
#eval [P 4 0,P 3 1, P 2 2, P 1 3, P 0 4]

-- Example
lemma P_le_fact (a b : ℕ) : P a b ≤ (a+b)! := by
  fun_induction P
  · simp only [add_zero]
    exact fact x
  · simp only [Nat.succ_eq_add_one, zero_add]
    exact fact (n + 1)
  · grw [ih1,ih2]
    simp only [Nat.succ_eq_add_one]
    grind [fact,factorial] -- grind for algebraic proofs

-- grind is a powerful automation
-- We will not be using grind for the rest of the week.
lemma P_le_fact'' (a b : ℕ) : P a b ≤ (a+b)! := by
  fun_induction P <;> all_goals grind only [fact, factorial]

-- This proof is more intuitive than the one-line proof
lemma P_le_fact' (a b : ℕ) : P a b ≤ (a+b)! := by
  fun_induction P
  · simp [fact]
  · simp [fact]
  · rename' a_1 => a, b_1 => b
    calc
      P (a + 1) b + P a (b + 1) ≤ (a + 1 + b) ! + (a + (b + 1)) !                            := by gcongr
                              _ ≤ (a + b) * (a + b + 1) ! + (a + 1 + b) ! + (a + (b + 1)) !  := by omega
                              _ = ((a + b + 1) + 1) * (a + b + 1)!                           := by ring_nf
                              _ = ((a + b + 1) + 1)!                                         := by bound
                              _ = (a + 1 + (b + 1))!                                         := by ring_nf


-- # Exercise 5
def isEven (n : ℕ) : Prop := ∃ k, n = 2*k
theorem isEven_iff (n : ℕ) : isEven (n)! ↔ n ≥ 2 := by sorry


-- # Exercise 6
/-
Define T(m,n):
  T(m,0) = T(0,n) = 1,
  T(m,n) = T(m-1,n) + T(m,n-1)
  Prove that T(m,n) ≤ 2^{m+n}
-/

def T : ℕ → ℕ  → ℕ := sorry
theorem solve_T (m n: ℕ):  T m n ≤ 2^(m+n)  := by sorry

/-
# Functional Induction on recursively defined function
Functional induction is useful especially for recursive functions.
-/

-- ## Lists
def append {α : Type} : List α → List α → List α
| [], bs => bs
| a :: as, bs => a :: (append as bs)

#check append
#eval append [1, 2, 3] [4, 5, 6]
-- In Mathlib, append has notation ++

#eval [1,2,10,3] ++ [4,5,6]

-- # Example: compute the length of a list
def len {α : Type} : List α → ℕ
| []     =>  0
| _ :: xs => 1 + len xs

#check len
#check len.induct

-- proof by functional induction
theorem len_append_fun_induction (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  fun_induction len
  · simp [len]
  · -- use rw?? to find pattern you want
    rw [List.cons_append]
    simp only [len]
    rw [ih1]

-- proof by functional induction one line
-- Remark: less understandable
theorem len_append_fun_induction_oneline (x : ℕ) (l : List ℕ) : len (l ++ [x]) = 1 + len l  := by
  fun_induction len l <;> all_goals grind [len]


-- # Exercise 7: write foldl
-- The foldl function (also known as reduce or fold-left)
-- combines the elements of a list using a binary operator,
-- starting from an initial value. It "folds" the list into a single value.
-- f: the combining function (accumulator -> element -> new_accumulator)
-- b: the initial base value (accumulator)

def my_foldl {α β : Type} (f : β → α → β) (b : β) : List α → β
| [] => b
| a :: as => sorry

example: my_foldl (fun acc x => acc + x) 0 [1, 2, 3, 4] = 10 := sorry
example: my_foldl (fun acc x => x :: acc) ([] : List Nat) [1, 2, 3] = [3, 2, 1] := sorry

-- Theorem
theorem foldl_append {α β : Type} (f : β → α → β) (b : β) (l1 l2 : List α) :
  my_foldl f b (l1 ++ l2) = my_foldl f (my_foldl f b l1) l2 := by
    revert b
    sorry
