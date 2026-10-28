import Mathlib.Tactic
import Cslib.Algorithms.Lean.TimeM
import waterfall
import Lectures.Week07.Sheet3

set_option autoImplicit false
set_option tactic.hygienic false

open Cslib.Algorithms.Lean

#check TimeM
open TimeM
/-- Recurrence relation for the time complexity of merge sort.
For a list of length `n`, this counts the total number of comparisons:
- Base cases: 0 comparisons for lists of length 0 or 1
- Recursive case: split the list, sort both halves,
  then merge (which takes at most `n` comparisons) -/
def timeMergeSortRec : ℕ → ℕ
| 0 => 0
| 1 => 0
| n@(_+2) => timeMergeSortRec (n/2) + timeMergeSortRec ((n-1)/2 + 1) + n

open Nat (clog)

/-- Key Lemma: ⌈log2 ⌈n/2⌉⌉ ≤ ⌈log2 n⌉ - 1 for n > 1 -/
@[grind →]
lemma clog2_half_le (n : ℕ) (h : n > 1) : clog 2 ((n + 1) / 2) ≤ clog 2 n - 1 := by
  grind [Nat.clog_of_one_lt one_lt_two h]

/-- Same logic for the floor half: ⌈log2 ⌊n/2⌋⌉ ≤ ⌈log2 n⌉ - 1 -/
@[grind →]
lemma clog2_floor_half_le (n : ℕ) (h : n > 1) : clog 2 (n / 2) ≤ clog 2 n - 1 := by
  apply Nat.le_trans _ (clog2_half_le n h)
  apply Nat.clog_monotone
  grind

private lemma some_algebra (n : ℕ) :
    (n / 2 + 1) * clog 2 (n / 2 + 1) + ((n + 1) / 2 + 1) * clog 2 ((n + 1) / 2 + 1) + (n + 2) ≤
    (n + 2) * clog 2 (n + 2) := by
  -- 1. Substitution: Let N = n_1 + 2 to clean up the expression
  let N := n + 2
  have hN : N ≥ 2 := by omega
  -- 2. Rewrite the terms using N
  have t1 : n / 2 + 1 = N / 2 := by omega
  have t2 : (n + 1) / 2 + 1 = (N + 1) / 2 := by omega
  have t3 : n + 1 + 1 = N := by omega
  let k := clog 2 N
  have h_bound_l : clog 2 (N / 2) ≤ k - 1 := clog2_floor_half_le N hN
  have h_bound_r : clog 2 ((N + 1) / 2) ≤ k - 1 := clog2_half_le N hN
  have h_split : N / 2 + (N + 1) / 2 = N := by omega
  grw [t1, t2, t3, h_bound_l, h_bound_r, ←Nat.add_mul, h_split]
  exact Nat.le_refl (N * (k - 1) + N)

/-- Upper bound function for merge sort time complexity: `T(n) = n * ⌈log₂ n⌉` -/
abbrev T (n : ℕ) : ℕ := n * clog 2 n

/-- Solve the recurrence -/
theorem timeMergeSortRec_le (n : ℕ) : timeMergeSortRec n ≤ T n := by
  fun_induction timeMergeSortRec with
  | case1 => grind
  | case2 => grind
  | case3 n ih2 ih1 =>
    grw [ih1,ih2]
    have := some_algebra n
    grind [Nat.add_div_right]

-- Exercise
theorem merge_ret_length_eq_sum (xs ys : List ℕ) :
    (merge xs ys).ret.length = xs.length + ys.length := sorry

-- Exercise
@[simp] theorem mergeSort_same_length (xs : List ℕ) :
    (mergeSort xs).ret.length = xs.length := sorry

-- Exercise
@[simp] theorem merge_time (xs ys : List ℕ) : (merge xs ys).time ≤ xs.length + ys.length := sorry

-- Relate the algorithm with recurrence relation.
theorem mergeSort_time_le (xs : List ℕ) :
    (mergeSort xs).time ≤ timeMergeSortRec xs.length := by
  fun_induction mergeSort with
  | case1 =>
    grind
  | case2 _ _ _ _ _ ih2 ih1 =>
    simp only [TimeM.time_bind]
    grw [merge_time]
    simp only [mergeSort_same_length]
    unfold timeMergeSortRec
    grind

/-- Time complexity of mergeSort -/
theorem mergeSort_time (xs : List ℕ) :
    let n := xs.length
    (mergeSort xs).time ≤ n * clog 2 n := by
  grind [mergeSort_time_le, timeMergeSortRec_le]
