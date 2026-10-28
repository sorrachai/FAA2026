import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM
import waterfall


-- Analysis of Insertion Sort
namespace mysorting

-- Define Insertion Sort
def insert (x : ℕ) (xs : List ℕ) : List ℕ :=
  match xs with
  | [] => [x]
  | y :: ys =>
    if x ≤ y then x :: xs
    else y :: insert x ys

def IS : List ℕ → List ℕ
 | [] => []
 | x :: xs =>
 let ret := IS xs
 insert x ret

#eval IS [5,10,2,3,9]
-- Let's state a sorted property using type

@[simp] abbrev Nat.leqAll (a : ℕ) (t : List ℕ) : Prop := ∀ y ∈ t, a ≤ y

-- Property of sortedness
inductive sorted : List ℕ → Prop
| empty : sorted []
| min (a : ℕ ) (t : List ℕ) : Nat.leqAll a t → sorted t → sorted (a :: t)

theorem sorted_sublist (y : ℕ) (ys : List ℕ) (h : sorted (y :: ys)) : Nat.leqAll y ys ∧ sorted ys := by
  cases h
  expose_names
  exact ⟨h_1, h⟩

theorem sorted_xyys_of_sorted_yys (x y : ℕ) (ys : List ℕ) (h_1 : x ≤ y) (h : sorted (y :: ys)) :
  sorted (x :: y :: ys) := by
  apply sorted_sublist at h
  apply sorted.min
  · simp_all only [Nat.leqAll, List.mem_cons, forall_eq_or_imp, true_and]
    intro a ha
    obtain ⟨h,_⟩ := h
    have: y ≤ a := by simp_all
    exact Nat.le_trans h_1 (h a ha)
  · exact sorted.min y ys h.1 h.2

theorem sorted_y_insert (x y : ℕ) (ys : List ℕ) (h_1 : y < x) (h2 : sorted (insert x ys))
  (h : Nat.leqAll y ys) : sorted (y :: insert x ys) := by
  fun_induction insert
  · simp_all only [Nat.leqAll, List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    refine sorted_xyys_of_sorted_yys y x [] (by omega) h2
  · expose_names
    refine sorted_xyys_of_sorted_yys y x (y_1 :: ys) (by omega) h2
  · expose_names
    refine sorted_xyys_of_sorted_yys y y_1 (insert x ys) ?_ h2
    simp_all

lemma insert_into_sorted (x : ℕ) (xs : List ℕ) (h : sorted xs) : sorted (insert x xs) := by
  fun_induction insert
  · apply sorted.min
    · simp
    · exact sorted.empty
  · expose_names
    exact sorted_xyys_of_sorted_yys x y ys h_1 h
  · expose_names
    apply sorted_sublist at h
    simp_all only [not_le, forall_const]
    refine sorted_y_insert x y ys h_1 ih1 h.1

-- Time complexity
open Cslib.Algorithms.Lean
#check TimeM

-- Define Insertion Sort with TimeM
def insertT (x : ℕ) (xs : List ℕ) : TimeM ℕ (List ℕ) :=
  match xs with
  | [] => return [x]
  | y :: ys => do
    ✓ let c := x ≤ y
    if c then return (x :: xs)
    else
    let ret ← insertT x ys
    return  y :: ret

-- # interpretation in each line
-- If the return type is a monad, say (`List ℕ`), then
-- `let ret ← insertT left`
-- This line means you can treat `ret` as type `List ℕ` and
-- let notation tell Lean to put `sortedLeft` into a box
-- If the return type is not a monad, you can use normal `let` with `:=` notation.

def IST : List ℕ → TimeM ℕ (List ℕ)
 | [] => return []
 | x :: xs =>  do
 let rest ← IST xs
 insertT x rest

theorem insert_eq_insertT (x : ℕ) (xs : List ℕ) : (insertT x xs).ret = insert x xs := by waterfall

theorem correct_IST (xs : List ℕ) : (IST xs).ret = IS xs := by
  fun_induction IST
  · rfl
  · expose_names
    simp only [TimeM.ret_bind, IS]
    rw [ih1]
    apply insert_eq_insertT

#eval IST [1,2,3,4]

theorem time_insert (x : ℕ) (xs : List ℕ) : (insertT x xs).time ≤ (xs.length) := by
  fun_induction insertT <;> grind

@[grind =] theorem insert_length_eq (y : ℕ) (ys : List ℕ) :
  (insertT y ys).ret.length = ys.length + 1  := by
  fun_induction insertT <;> grind

lemma list_length (xs : List ℕ) : (IST xs).ret.length = xs.length := by
  fun_induction IST <;> grind

theorem time_IS (xs : List ℕ) : (IST xs).time ≤ (xs.length) * (xs.length) := by
  fun_induction IST
  · rfl
  · expose_names
    simp_all only [TimeM.time_bind, List.length_cons]
    grw [time_insert,ih1, list_length]
    ring_nf
    omega

end mysorting
