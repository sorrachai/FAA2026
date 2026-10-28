import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM
import waterfall

set_option autoImplicit false
set_option tactic.hygienic false

open Cslib.Algorithms.Lean
#check TimeM

-- Analysis of merge sort
def merge : List ℕ → List ℕ → TimeM ℕ (List ℕ)
  | [], ys => return ys
  | xs, [] => return xs
  | x::xs', y::ys' => do
    ✓ let c := (x ≤ y)
    if c then
      let rest ← merge xs' (y::ys')
      return (x :: rest)
    else
      let rest ← merge (x::xs') ys'
      return (y :: rest)

def mergeSort (xs : List ℕ) : TimeM ℕ (List ℕ) :=  do
  if xs.length < 2 then return xs
  else
    let n := xs.length
    let half := n / 2
    let left :=  xs.take half
    let right := xs.drop half
    let sortedLeft ← mergeSort left
    let sortedRight ← mergeSort right
    merge sortedLeft sortedRight

-- # interpretation in each line
-- If the return type is a monad, say (`List ℕ`), then
-- `let sortedLeft ← mergeSort left`
-- This line means you can treat `sortedLeft` as type List ℕ and let notation tell Lean to put `sortedLeft` into a box
-- If the return type is not a monad, you can use normal `let` with `:=` notation.

#check mergeSort
#eval merge [1,2,3,10] [4,5]
#eval mergeSort [4,2,3,1]

-- Correctnes of Merge sort

@[simp, grind] def Nat.MinOfList (a :ℕ ) (t: List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- inductive predicate
inductive Sorted : List ℕ → Prop
  | nil : Sorted []
  | single (a : ℕ) : Sorted [a]
  | cons (a b : ℕ) (t : List ℕ ) : a ≤ b → Sorted (b :: t) → Sorted (a :: b :: t)
  | cons_min (a :ℕ) (t : List ℕ) : a.MinOfList t → Sorted (t) →  Sorted (a :: t)

theorem sorted_min {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) :  x.MinOfList xs  := by
  cases hxs
  · simp
  · simp only [Nat.MinOfList, List.mem_cons, forall_eq_or_imp]
    constructor
    · exact a_1
    · apply sorted_min at a_2
      grind
  · exact a_1

theorem sorted_is_preserved_by_min_cons {a : ℕ} {t : List ℕ} (hmin : a.MinOfList t) (ht : Sorted t) : Sorted (a :: t) := by
  exact Sorted.cons_min a t hmin ht

theorem sorted_suffix {x : ℕ} {xs : List ℕ} (hxs : Sorted (x :: xs)) : Sorted xs := sorry

-- Exercise: Port your the proof of merge sort in the previous lectures into this proof.

theorem mem_either_merge (xs ys : List ℕ) (z : ℕ)
  (hz : z ∈ (merge xs ys).ret) : z ∈ xs ∨ z ∈ ys := by sorry

theorem min_all_merge (x : ℕ) (xs ys : List ℕ)
(hxs : x.MinOfList xs) (hys : x.MinOfList ys) : x.MinOfList (merge xs ys).ret := by sorry

theorem sorted_merge {l1 l2 : List ℕ} (hxs : Sorted l1)
  (hys : Sorted l2) : Sorted ((merge l1 l2).ret) := by sorry

-- Let's do this one as an example.
theorem MSMCorrect (xs : List ℕ) : Sorted (mergeSort xs).ret := by sorry
