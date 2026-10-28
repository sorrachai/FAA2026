import Mathlib
import Cslib.Algorithms.Lean.TimeM
import waterfall

set_option autoImplicit false
set_option tactic.hygienic false

open Cslib.Algorithms.Lean

namespace exercise

/-- A three-way comparison: `-1` for less than, `0` for equal, and `1` for greater than. -/
def compareNat (x y : ℕ) : ℤ :=
  if x < y then -1 else if x = y then 0 else 1

@[simp] lemma compareNat_eq_neg_one_iff (x y : ℕ) :
    compareNat x y = -1 ↔ x < y := by
  simp [compareNat]
  omega

@[simp] lemma compareNat_eq_zero_iff (x y : ℕ) :
    compareNat x y = 0 ↔ x = y := by
  simp [compareNat]
  omega

@[simp] lemma compareNat_eq_one_iff (x y : ℕ) :
    compareNat x y = 1 ↔ y < x := by
  simp [compareNat]
  omega

inductive BinaryTree where
  | nil
  | node (value : ℕ) (left right : BinaryTree)

def inorder : BinaryTree → List ℕ
  | .nil => []
  | .node value l r => inorder l ++ value :: inorder r

namespace BinaryTree

def height : BinaryTree → ℕ
  | .nil => 0
  | .node _ l r => 1 + max l.height r.height

end BinaryTree

def bstFindT (q : ℕ) : BinaryTree → TimeM ℕ Bool
  | .nil => return false
  | .node x l r => do
      ✓ let c := compareNat q x
      if c = 0 then return true
      else if c = -1 then bstFindT q l
      else bstFindT q r
/-!
Exercise: Size of a binary tree

We count the nodes of a binary tree. Visiting one node costs one time unit.
-/

def sizeT : BinaryTree  → TimeM ℕ ℕ
| .nil => return 0
| .node _ l r => do
  ✓
  let nl ← sizeT l
  let nr ← sizeT r
  return nl + nr + 1

/-!
Task (a): Prove that sizeT counts the nodes and visits each node once.
-/
theorem sizeT_correct (t : BinaryTree) :
(sizeT t).ret = (inorder t).length := by
  sorry

theorem sizeT_time (t : BinaryTree) :
(sizeT t).time = (inorder t).length := by
  sorry

/-!
Task (b): Prove that a tree is never higher than it has nodes.
-/
lemma height_le_length (t : BinaryTree) :
t.height ≤ (inorder t).length := by
  sorry

/-!
Task (c): Conclude that lookup in a BST takes at most linear time
in the number of nodes.
-/
theorem bstFindT_time_le_length (q : ℕ) (t : BinaryTree) :
  (bstFindT q t).time ≤ (inorder t).length := by
  sorry

end exercise
