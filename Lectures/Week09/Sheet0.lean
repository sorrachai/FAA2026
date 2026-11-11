/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Lectures.Week09.Sheet1

set_option autoImplicit false

/-!
# Week 09, Sheet 0: BFS termination support

This file proves termination facts for a neighbor scanner, given its equations
for the empty list and a nonempty list. The scanner itself is defined in Sheet 2,
which supplies these equations by reflexivity. Thus Sheet 2 can display the
complete algorithm while importing the longer termination proofs from here.
-/

namespace SimpleDiGraph

variable {n : ℕ}

/-- Count marked vertices for the termination measure only.
The executable BFS loop never computes this count. -/
def markedCount (visited : Vector Bool n) : ℕ :=
  (Finset.univ.filter (fun v : Fin n => visited[v.val] = true)).card

private lemma markedCount_le (visited : Vector Bool n) : markedCount visited ≤ n := by
  simpa [markedCount] using
    (Finset.card_le_univ (Finset.univ.filter (fun v : Fin n => visited[v.val] = true)))

private lemma markedCount_set (visited : Vector Bool n) (a : Fin n)
    (ha : visited[a.val] ≠ true) :
    markedCount (visited.set a.val true) = markedCount visited + 1 := by
  have hs : Finset.univ.filter (fun v : Fin n => (visited.set a.val true)[v.val] = true) =
      insert a (Finset.univ.filter (fun v : Fin n => visited[v.val] = true)) := by
    ext v
    by_cases hav : a = v
    · subst v
      simp
    · have hval : a.val ≠ v.val := fun h => hav (Fin.ext h)
      simp [hval, Ne.symm hav]
  unfold markedCount
  rw [hs, Finset.card_insert_of_notMem]
  simpa using ha

section Scan

variable
  (scan : List (Fin n) → Array (Fin n) → Vector Bool n →
    Array (Fin n) × Vector Bool n)
  (scan_nil : ∀ queue visited, scan [] queue visited = (queue, visited))
  (scan_cons : ∀ a vs queue visited,
    scan (a :: vs) queue visited =
      if visited[a.val] then
        scan vs queue visited
      else
        scan vs (queue.push a) (visited.set a.val true))

include scan_nil scan_cons

private lemma scan_size (vs : List (Fin n))
    (queue : Array (Fin n)) (visited : Vector Bool n) :
    queue.size ≤ (scan vs queue visited).1.size := by
  induction vs generalizing queue visited with
  | nil => simp [scan_nil]
  | cons a vs ih =>
      by_cases ha : visited[a.val] = true
      · simpa [scan_cons, ha] using ih queue visited
      · rw [scan_cons, if_neg ha]
        have h := ih (queue.push a) (visited.set a.val true)
        simp only [Array.size_push] at h
        omega

/-- Discovering a vertex increases both the marked count and queue size by one. -/
private lemma scan_balance (vs : List (Fin n))
    (queue : Array (Fin n)) (visited : Vector Bool n) :
    markedCount (scan vs queue visited).2 + queue.size =
      markedCount visited + (scan vs queue visited).1.size := by
  induction vs generalizing queue visited with
  | nil => simp [scan_nil]
  | cons a vs ih =>
      by_cases ha : visited[a.val] = true
      · simpa [scan_cons, ha] using ih queue visited
      · have h := ih (queue.push a) (visited.set a.val true)
        simp only [Array.size_push, markedCount_set visited a ha] at h
        simp only [scan_cons, if_neg ha]
        omega

/-- Scanning neighbors and advancing the head strictly decreases the sum of
unvisited vertices and pending queue entries. -/
lemma bfs_measure_decreases (vs : List (Fin n)) (head : ℕ)
    (queue : Array (Fin n)) (visited : Vector Bool n) (hhead : head < queue.size) :
    n - markedCount (scan vs queue visited).2 +
        ((scan vs queue visited).1.size - (head + 1)) <
      n - markedCount visited + (queue.size - head) := by
  have hbalance := scan_balance scan scan_nil scan_cons vs queue visited
  have hsize := scan_size scan scan_nil scan_cons vs queue visited
  have hmarked := markedCount_le visited
  have hmarked' := markedCount_le (scan vs queue visited).2
  omega

end Scan

end SimpleDiGraph
