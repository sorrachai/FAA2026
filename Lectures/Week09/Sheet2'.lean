/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Lectures.Week09.Sheet1

set_option autoImplicit false

/-!
# BFS through mathematical invariants

The goal is to make the mathematical proof visible before dealing with arrays.
Vertex labels lie in `Fin n`, which already has instances for finiteness and
decidable equality. The queue Q is a list, and the visited set S is a `Finset`.
Here "visited" means **discovered**, not necessarily already processed.
Vertices are marked when added to the queue.

We maintain two invariants:

1. Q ⊆ S: every queued vertex has already been discovered.
2. Every s ∈ S is reachable from the starting vertex r.

These imply that the next queued vertex is reachable. Its outgoing neighbors
are then reachable by extending a walk by one edge. This is the entire graph
argument; the remaining work is checking that the two invariants survive.

-/

namespace SimpleDiGraph.MathematicalBFS

variable {n : ℕ}

/-! ## 1. The mathematical state and one BFS step

For the current head u, let

  NN(u) = N⁺(u) \ S,
  Q'    = qt ++ NN(u).toList,
  S'    = S ∪ NN(u),

where Q = u :: qt and N⁺(u) is the set of outgoing neighbors of u.
The list conversion puts each new neighbor in the queue exactly once; its order
does not matter for the soundness proof.

Although adjacency is a proposition, `[DecidableRel G.Adj]` supplies a decision
procedure for each pair of vertices. This lets us compute the neighbor finset
by filtering `Finset.univ`, without using classical choice.

We use `Finset.toList` to append the new neighbors to the queue without
prescribing an order for the queue. This conversion chooses a list
noncomputably, so `bfs_rec` and `bfs` are marked `noncomputable`. The neighbor
definition itself remains computable with the adjacency hypothesis. We still prove termination
and soundness in full; `noncomputable` does not weaken these obligations.
Sheet 3 gives the executable array-based implementation with adjacency lists.
-/

/-- The finite set of outgoing neighbors of u. -/
def outNeighbors (G : SimpleDiGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) : Finset (Fin n) := {v | G.Adj u v}

@[simp] lemma mem_outNeighbors (G : SimpleDiGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) :
    v ∈ outNeighbors G u ↔ G.Adj u v := by
  simp [outNeighbors]

/-! ## 2. Why the recursion terminates

There are n possible vertex labels. Use the nonnegative measure

  μ(Q, S) = n - |S| + length Q.

Suppose k new vertices are discovered when u is removed. The new vertices are
disjoint from S, so |S'| = |S| + k and length Q' = length Q - 1 + k.
Thus μ(Q', S') + 1 = μ(Q, S): every iteration decreases the measure by one.
The bound |S'| ≤ n justifies this calculation with natural-number subtraction.

This proves termination, not that there are always n iterations. The queue can
become empty while some vertices remain undiscovered.
-/

/-- The newly discovered vertices cancel from the two parts of the measure. -/
lemma measure_step (visited new_neighbors : Finset (Fin n)) (u : Fin n) (qt : List (Fin n))
    (hdisjoint : Disjoint visited new_neighbors) :
    n - (visited ∪ new_neighbors).card +
        (qt ++ new_neighbors.toList).length + 1 =
      n - visited.card + (u :: qt).length := by
  have hcard := Finset.card_union_of_disjoint hdisjoint
  have hbound : (visited ∪ new_neighbors).card ≤ n := by
    simpa using Finset.card_le_univ (visited ∪ new_neighbors)
  simp only [List.length_append, Finset.length_toList, List.length_cons]
  omega

lemma measure_decreases (visited new_neighbors : Finset (Fin n)) (u : Fin n) (qt : List (Fin n))
    (hdisjoint : Disjoint visited new_neighbors) :
    n - (visited ∪ new_neighbors).card +
        (qt ++ new_neighbors.toList).length <
      n - visited.card + (u :: qt).length := by
  have h := measure_step visited new_neighbors u qt hdisjoint
  omega

/-- The mathematical BFS loop: remove one vertex, append its new neighbors,
and add those neighbors to the visited set. -/
noncomputable def bfs_rec (G : SimpleDiGraph (Fin n)) [DecidableRel G.Adj]
    (queue : List (Fin n)) (visited : Finset (Fin n)) : Finset (Fin n) :=
  match queue with
  | [] => visited
  | u :: qt =>
      let new_neighbors := outNeighbors G u \ visited
      let queue' := qt ++ new_neighbors.toList
      let visited' := visited ∪ new_neighbors
      bfs_rec G queue' visited'
termination_by n - visited.card + queue.length
decreasing_by
  exact measure_decreases visited (outNeighbors G u \ visited) u qt
    Finset.disjoint_sdiff

/-- Start with the root discovered and waiting to be processed. -/
noncomputable def bfs (G : SimpleDiGraph (Fin n)) [DecidableRel G.Adj]
    (r : Fin n) : Finset (Fin n) :=
  bfs_rec G [r] {r}

/-! ## 3. The only graph fact we need

If r reaches u and u has an outgoing edge to w, concatenate a walk from r to u
with that edge. This uses the edge in its given direction; no reverse walk or
connectivity assumption is needed.
-/

lemma reachable_step (G : SimpleDiGraph (Fin n)) {r u w : Fin n}
    (hu : G.Reachable r u) (huw : G.Adj u w) : G.Reachable r w := by
  obtain ⟨p⟩ := hu
  have hw : w ∈ G.vertexSet := (G.incidence _ huw).2
  exact ⟨p.append (.cons huw (.nil hw))⟩



/-! ## 4. The mathematical invariant proof

Assume Q ⊆ S and every element of S is reachable from r.

* If Q is empty, BFS returns S, whose elements are reachable by assumption.
* Otherwise Q = u :: qt. Since u ∈ Q ⊆ S, the visited invariant gives r ↝ u.
  Every w ∈ NN(u) is an outgoing neighbor of u, so r ↝ u → w.
  We now check the two invariants for the recursive call:

  - Every element of S' = S ∪ NN(u) is reachable: use the old invariant for S
    and the one-edge extension argument for NN(u).
  - Every element of Q' = qt ++ NN(u).toList lies in S': an old queue entry
    lies in S, and a new queue entry lies in NN(u).

Apply the same preservation lemma to the smaller state (Q', S'). This is the
recursive proof style of the 2025 sheet. Its termination uses the very same
measure lemma as the algorithm, with both termination obligations discharged.

In Lean, `∀ x ∈ queue, x ∈ visited` expresses Q ⊆ S even though Q is a list
and S is a finset. No duplicate-free queue hypothesis is needed for soundness.
-/

/-- If the current state satisfies both invariants, every vertex returned by
this call is reachable from the original root. -/
lemma bfs_rec_preserves_invariants (G : SimpleDiGraph (Fin n)) [DecidableRel G.Adj]
    (r : Fin n)
    (queue : List (Fin n)) (visited : Finset (Fin n))
    (hvisited_reachable : ∀ x ∈ visited, G.Reachable r x)
    (hqueue_subset_visited : ∀ x ∈ queue, x ∈ visited) :
    ∀ x ∈ bfs_rec G queue visited, G.Reachable r x := by
    fun_induction bfs_rec
    · expose_names
      simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
    · expose_names
      apply ih1
      · intro x hx
        simp only [Finset.mem_union, visited'] at hx
        cases hx
        · rename_i h
          grind
        · rename_i h
          simp only [Finset.mem_sdiff, mem_outNeighbors, new_neighbors] at h
          have: G.Reachable r u := by grind
          apply reachable_step G this h.1
      · simp_all [visited',queue']
        grind


/-! ## 5. Initialization and the final theorem

Initially Q = [r] and S = {r}, so Q ⊆ S. The only discovered vertex is r,
which reaches itself by the walk of length zero. Since Sheet 1's graphs have
an explicit vertex set, this zero-edge walk requires r ∈ G.vertexSet.

The preservation lemma then gives the desired property of the final set.
Notice that the invariant is about the *current state*, while the conclusion
is about the *result of the entire remaining execution*.
-/

/-- Soundness: the mathematical BFS returns only vertices reachable from r. -/
theorem bfs_sound (G : SimpleDiGraph (Fin n)) [DecidableRel G.Adj]
    (r : Fin n) (hr : r ∈ G.vertexSet) :
    ∀ v ∈ bfs G r, G.Reachable r v := by
  apply bfs_rec_preserves_invariants
  · simp only [Finset.mem_singleton, forall_eq]
    simp only [Reachable]
    refine Nonempty.intro ?_
    exact Walk.nil hr
  · simp only [List.mem_cons, List.not_mem_nil, or_false, Finset.mem_singleton, imp_self,
    implies_true]

/-- Completeness: BFS returns every vertex reachable from the root. -/
-- Exercise
theorem bfsVertices_complete (G : SimpleDiGraph (Fin n)) (r v : Fin n) [DecidableRel G.Adj] :
    G.Reachable r v → v ∈ bfs G r := by sorry

end SimpleDiGraph.MathematicalBFS
