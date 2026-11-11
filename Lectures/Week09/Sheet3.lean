/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Lectures.Week09.Sheet0

set_option autoImplicit false

open SimpleDiGraph

/-!
# BFS with arrays

The vertices are all array indices 0, ..., n - 1, each of type `Fin n`.
An index with no incident edges represents an isolated vertex.
Store the outgoing adjacency lists in an array, and use a Boolean array for
visited flags. The queue is another array: enqueue pushes at its end, and a
head index advances through it without removing or shifting entries.

`Vector α n` is Lean's array of fixed length n (an Array with a size proof).
The proof is erased at runtime; indexing and updating use the underlying array.
Our goal is soundness: every vertex returned by BFS is reachable from the root,
using Sheet 1's definition of a directed walk:

  v ∈ bfsVertices g r → g.toSimpleDiGraph.Reachable r v
-/

namespace SimpleDiGraph

variable {n : ℕ}

/-! ## 1. An array of adjacency lists -/

/-- Every index in Fin n is a vertex, including isolated vertices.
Each adjacency list contains no repetitions. -/
structure AdjListGraph (n : ℕ) where
  neighbors : Vector (List (Fin n)) n
  loopless : ∀ a b : Fin n, b ∈ neighbors[a] → a ≠ b
  -- The BFS algorithm does not need this property
  nodup : ∀ a : Fin n, (neighbors[a]).Nodup

def AdjListGraph.toSimpleDiGraph (g : AdjListGraph n) : SimpleDiGraph (Fin n) where
  vertexSet := Set.univ
  edgeSet := {e | e.2 ∈ g.neighbors[e.1]}
  incidence := fun _ _ => ⟨Set.mem_univ _, Set.mem_univ _⟩
  loopless := fun e he => g.loopless e.1 e.2 he

/-! ## 2. The algorithm -/

/-- Scan neighbors from left to right. Mark each new vertex before enqueueing
it, so later occurrences see the updated flag. Both arrays are threaded forward. -/
def enqueueNeighbors : List (Fin n) → Array (Fin n) → Vector Bool n →
    Array (Fin n) × Vector Bool n
  | [],      queue, visited => (queue, visited)
  | v :: vs, queue, visited =>
      if visited[v] then
        enqueueNeighbors vs queue visited
      else
        enqueueNeighbors vs (queue.push v) (visited.set v true)

@[simp] lemma marked_set (visited : Vector Bool n) (a b : Fin n) :
    (visited.set a true)[b] = true ↔ b = a ∨ visited[b] = true := by
  by_cases hab : a = b
  · subst b
    simp
  · simp [← Fin.ext_iff, hab, Ne.symm hab]

/-!
Sheet 0 proves termination for any scanner satisfying these recursion equations.
In `decreasing_by`, the two `rfl` proofs supply the equations of `enqueueNeighbors`.
The annotation `(eq := hnext)` records the returned pair for the termination proof.
-/

/-- Expand queued vertices until head reaches the end of the queue. -/
def bfs_rec (g : AdjListGraph n) (head : ℕ)
    (queue : Array (Fin n)) (visited : Vector Bool n) : Vector Bool n :=
  if h : head < queue.size then
    let v := queue[head]
    let (eq := hnext) ⟨queue', visited'⟩ :=
      enqueueNeighbors g.neighbors[v] queue visited
    bfs_rec g (head + 1) queue' visited'
  else
    visited
termination_by n - markedCount visited + (queue.size - head)
decreasing_by
  simpa only [hnext] using
    bfs_measure_decreases enqueueNeighbors
      (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      g.neighbors[v] head queue visited h

/-- Start with the root marked and queued; return the final visited flags. -/
def bfsFlags (g : AdjListGraph n) (r : Fin n) : Vector Bool n :=
  bfs_rec g 0 #[r] ((Vector.replicate n false).set r true)

/-- Enumerate the marked indices once, after the search. -/
def bfsVertices (g : AdjListGraph n) (r : Fin n) : Finset (Fin n) :=
  let visited := bfsFlags g r
  {v | visited[v] = true}

namespace BFSExamples

/-- 0 → 1 → 2, together with the isolated vertex 3. -/
def directedPath : AdjListGraph 4 where
  neighbors := #v[[1], [2], [], []]
  loopless := by decide
  nodup := by decide

#eval (bfsFlags directedPath 0).toArray -- #[true, true, true, false]
#eval bfsVertices directedPath 0 -- {0, 1, 2}
#eval bfsVertices directedPath 1 -- {1, 2}
#eval bfsVertices directedPath 2 -- {2}: a sink is still a vertex
#eval bfsVertices directedPath 3 -- {3}: an isolated vertex reaches itself

end BFSExamples

/-! ## 3. Extending a reachable walk

The easy direction is soundness: BFS only discovers reachable vertices.
Whenever we scan the neighbors of a reachable vertex, each neighbor is reachable
by appending one edge to the walk that reaches the current vertex.
-/

/-- Extend a reachable walk by one directed edge. -/
lemma reachable_step {V : Type*} (G : SimpleDiGraph V) {r a b : V}
    (ha : G.Reachable r a) (hab : G.Adj a b) : G.Reachable r b := by
  obtain ⟨p⟩ := ha
  exact ⟨p.append (.cons hab (.nil (G.incidence _ hab).2))⟩

/-! ## 4. Scanning neighbors preserves the two invariants

Let S be the set of marked vertices and Q the vertices in the queue array.
We maintain two facts: Q ⊆ S, and every vertex in S is reachable from the root.
In Sheet 2, Q is the list of pending vertices. Here the array keeps processed
entries too; Q ⊆ S holds for all its entries, and therefore also for the
unprocessed suffix starting at head.

Sheet 2 updates S and Q in bulk. Here `enqueueNeighbors` performs those updates
one neighbor at a time. Scanning a list of reachable neighbors preserves both
facts. An already marked neighbor changes neither array. A new neighbor is
marked before it is enqueued:
old queue entries remain marked, the new entry is marked, and its reachability
extends the invariant for S. The proof follows recursion on the neighbor list.
As in Sheet 2, we name the two hypotheses `hvisited_reachable` and
`hqueue_subset_visited`, and establish them again for the updated state.
The conclusion returns these two facts in that order.
-/

lemma enqueueNeighbors_sound (g : AdjListGraph n) (r : Fin n)
    (vs : List (Fin n))
    (queue : Array (Fin n)) (visited : Vector Bool n)
    (hnew_reachable : ∀ v ∈ vs, g.toSimpleDiGraph.Reachable r v)
    (hvisited_reachable : ∀ v : Fin n, visited[v] = true →
      g.toSimpleDiGraph.Reachable r v)
    (hqueue_subset_visited : ∀ v ∈ queue, visited[v] = true) :
    (∀ v : Fin n, (enqueueNeighbors vs queue visited).2[v] = true →
      g.toSimpleDiGraph.Reachable r v) ∧
    (∀ v ∈ (enqueueNeighbors vs queue visited).1,
      (enqueueNeighbors vs queue visited).2[v] = true) := by
  induction vs generalizing queue visited with
  | nil =>
      exact ⟨hvisited_reachable, hqueue_subset_visited⟩
  | cons a vs ih =>
      have ha_reachable : g.toSimpleDiGraph.Reachable r a :=
        hnew_reachable a (List.Mem.head vs)
      have htail_reachable : ∀ v ∈ vs, g.toSimpleDiGraph.Reachable r v :=
        fun v hv => hnew_reachable v (List.mem_cons_of_mem a hv)
      by_cases hmark : visited[a] = true
      · -- An already discovered neighbor leaves both invariants unchanged.
        simpa only [enqueueNeighbors, if_pos hmark] using
          ih queue visited htail_reachable hvisited_reachable hqueue_subset_visited
      · let queue' := queue.push a
        let visited' := visited.set a true
        -- Preserve reachability of S': a is reachable, and old marks stay sound.
        have hvisited'_reachable : ∀ v : Fin n, visited'[v] = true →
            g.toSimpleDiGraph.Reachable r v := by
          intro v hv
          rcases (marked_set visited a v).mp hv with rfl | hv
          · exact ha_reachable
          · exact hvisited_reachable v hv
        -- Preserve Q' ⊆ S': old entries stay marked, and a is marked now.
        have hqueue'_subset_visited' : ∀ v ∈ queue', visited'[v] = true := by
          intro v hv
          rcases Array.mem_push.mp hv with hv | rfl
          · exact (marked_set visited a v).mpr (Or.inr (hqueue_subset_visited v hv))
          · simp [visited']
        -- Continue scanning with exactly the same two invariant hypotheses.
        simpa only [enqueueNeighbors, if_neg hmark] using
          ih queue' visited' htail_reachable hvisited'_reachable hqueue'_subset_visited'

/-! ## 5. The same invariant proof as in Sheet 2

Use `fun_induction bfs_rec`, just as in Sheet 2, with the same two named
hypotheses: every marked vertex is reachable, and every queued vertex is marked.
In the recursive case, the next queued vertex is marked because Q ⊆ S, so
the visited-set invariant makes it reachable. Appending one edge shows that all
its outgoing neighbors are reachable. The scanning lemma then proves
reachability of S' and Q' ⊆ S',
supplying the two assumptions for the induction hypothesis in the same order
as Sheet 2. The equation `hnext` identifies these updated arrays with the pair
returned by the scanner.

When head reaches the end of the queue array, return the current flags;
the visited-set invariant already gives the desired conclusion.
-/

lemma bfs_rec_sound (g : AdjListGraph n) (r : Fin n) (head : ℕ)
    (queue : Array (Fin n)) (visited : Vector Bool n)
    (hvisited_reachable : ∀ v : Fin n, visited[v] = true → g.toSimpleDiGraph.Reachable r v)
    (hqueue_subset_visited : ∀ v ∈ queue, visited[v] = true) :
    ∀ v : Fin n, (bfs_rec g head queue visited)[v] = true →
      g.toSimpleDiGraph.Reachable r v := by
  fun_induction bfs_rec
  · expose_names
    -- First use Q ⊆ S, then use reachability of S, exactly as in Sheet 2.
    have hv_in_queue : v ∈ queue :=
      Array.mem_iff_getElem.mpr ⟨head, h, rfl⟩
    have hv_marked : visited[v] = true := hqueue_subset_visited v hv_in_queue
    have hv_reachable : g.toSimpleDiGraph.Reachable r v :=
      hvisited_reachable v hv_marked
    -- Every outgoing neighbor is reachable by one more directed edge.
    have hnew_reachable : ∀ w ∈ g.neighbors[v], g.toSimpleDiGraph.Reachable r w := by
      intro w hw
      exact reachable_step _ hv_reachable hw
    -- The scanner establishes both invariants for the updated arrays.
    have hnext_invariants := enqueueNeighbors_sound g r g.neighbors[v]
      queue visited hnew_reachable hvisited_reachable hqueue_subset_visited
    simp only [hnext] at hnext_invariants
    -- Apply the induction hypothesis with reachability first and Q' ⊆ S' second.
    exact ih1 hnext_invariants.1 hnext_invariants.2
  · -- No pending vertex remains, so return the current visited flags.
    exact hvisited_reachable

/-! ## 6. Main theorem: every returned vertex is reachable

Initially, the root is the only queued vertex and is already marked, so
Q ⊆ S. It is also the only marked vertex and is reachable by the walk of
length zero, establishing the second invariant. As in Sheet 2, apply the loop's
soundness lemma, then prove reachability of S and inclusion Q ⊆ S.
This theorem proves one direction only; completeness would additionally show
that every reachable vertex is eventually marked.
-/

/-- Soundness: every vertex returned by BFS is reachable from the root. -/
theorem bfsVertices_sound (g : AdjListGraph n) (r v : Fin n) :
    v ∈ bfsVertices g r → g.toSimpleDiGraph.Reachable r v := by
  intro hv
  unfold bfsVertices at hv
  have hflag : (bfsFlags g r)[v] = true := (Finset.mem_filter.mp hv).2
  unfold bfsFlags at hflag
  refine bfs_rec_sound g r 0 #[r] _ ?_ ?_ v hflag
  · -- Initially S = {r}, and the zero-edge walk reaches r.
    intro x hx
    have hxr : x = r := by
      simpa using (marked_set (Vector.replicate n false) r x).mp hx
    subst x
    exact ⟨.nil (Set.mem_univ _)⟩
  · -- Initially Q = [r], and r is already marked: Q ⊆ S.
    intro x hx
    have hxr : x = r := by simpa using hx
    subst x
    simp

/-- Completeness: BFS returns every vertex reachable from the root. -/
theorem bfsVertices_complete (g : AdjListGraph n) (r v : Fin n) :
    g.toSimpleDiGraph.Reachable r v → v ∈ bfsVertices g r := by sorry

/-- BFS returns a vertex if and only if it is reachable from the root. -/
theorem mem_bfsVertices_iff (g : AdjListGraph n) (r v : Fin n) :
    v ∈ bfsVertices g r ↔ g.toSimpleDiGraph.Reachable r v := by
  exact ⟨bfsVertices_sound g r v, bfsVertices_complete g r v⟩

end SimpleDiGraph
