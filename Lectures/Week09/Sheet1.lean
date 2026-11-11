/-
Copyright (c) 2026 Sorrachai Yingchareonthawornchai. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sorrachai Yingchareonthawornchai
-/

import Mathlib.Tactic
import waterfall

set_option autoImplicit false

/-!
# Week 09, Sheet 1: Simple directed graphs
-/

variable {α : Type*}

/-- A simple directed graph on `α` with edges as ordered pairs of distinct vertices. -/
-- We will use this definition throughout the lecture
structure SimpleDiGraph (α : Type*) where
  /-- The set of vertices. -/
  vertexSet : Set α
  /-- The set of directed edges. -/
  edgeSet : Set (α × α)
  /-- Both endpoints of every directed edge are vertices. Prefer `SimpleDiGraph.incidence`. -/
  incidence : ∀ e ∈ edgeSet, e.1 ∈ vertexSet ∧ e.2 ∈ vertexSet
  /-- No directed edge is a loop. Prefer `SimpleDiGraph.loopless`. -/
  loopless : ∀ e ∈ edgeSet, e.1 ≠ e.2

-- Modeling discussion

/-- A simple directed graph with vertex type `α`. -/
structure AdjDiGraph (α : Type*) where
  /-- A directed edge from u to v. -/
  Adj : α → α → Prop
  /-- No vertex has an edge to itself. -/
  loopless : ∀ u, ¬ Adj u u

-- Another good option
/-- A simple directed graph with an explicit vertex set. -/
structure SimpleDiGraph' (α : Type*) where
  vertexSet : Set α
  /-- A directed edge from u to v. -/
  Adj : α → α → Prop
  /-- Both endpoints of an edge belong to the graph. -/
  incidence : ∀ {u v}, Adj u v → u ∈ vertexSet ∧ v ∈ vertexSet
  /-- No vertex has an edge to itself. -/
  loopless : ∀ u, ¬ Adj u u

namespace SimpleDiGraph

/-- Notation for the vertex set of a graph. -/
scoped notation "V(" G ")" => vertexSet G
/-- Notation for the edge set of a graph. -/
scoped notation "E(" G ")" => edgeSet G


universe u

variable {V : Type u} (G : SimpleDiGraph V)

#check G

/-- Adjacency means that the ordered pair is a directed edge. -/
def Adj (u v : V) : Prop := (u, v) ∈ G.edgeSet

/-- The out-neighbors of `v`: vertices reached by one edge from `v`. -/
def neighborSet (v : V) : Set V := {w | G.Adj v w}

/-!
A walk follows the direction of every edge. Even a zero-edge walk must
start at an actual vertex of G, rather than an arbitrary value of type V.
-/
inductive Walk : V → V → Type u
  | nil {u : V} (hu : u ∈ G.vertexSet) : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w

def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)

/-- Every vertex can reach every other vertex in the directed graph.
This is strong connectivity without a nonemptiness requirement. -/
def PreConnected : Prop :=
  ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, G.Reachable u v

namespace Walk

variable {G}

/-- The length of a walk is the number of directed edges along it. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil _ => 0
  | cons _ q => q.length + 1

/-- The first vertex of a walk belongs to the graph. -/
theorem start_mem {u v : V} (p : G.Walk u v) : u ∈ G.vertexSet := by sorry
/-- The last vertex of a walk belongs to the graph. -/
theorem end_mem {u v : V} (p : G.Walk u v) : v ∈ G.vertexSet := by sorry

end Walk

/-- A directed triangle: 0 → 1 → 2 → 0. -/
def triangle : SimpleDiGraph (Fin 3) where
  vertexSet := Set.univ
  edgeSet := {(0, 1), (1, 2), (2, 0)}
  incidence := by
    intro e he
    exact ⟨Set.mem_univ _, Set.mem_univ _⟩
  loopless := by
    intro e he
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
    rcases he with rfl | rfl | rfl <;> decide

#check triangle

def triangle_walk : triangle.Walk 0 2 :=
  Walk.cons (by simp [Adj, triangle] : triangle.Adj 0 1)
    (Walk.cons (by simp [Adj, triangle] : triangle.Adj 1 2)
      (Walk.nil (by simp [triangle])))

#eval triangle_walk.length -- 2

namespace Walk

variable {G}

/-- The concatenation of two compatible directed walks. -/
@[trans]
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil _, q => q
  | cons h p, q => cons h (p.append q)

/-- Exercise: the length of appended walks is the sum of their lengths. -/
lemma length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by sorry

end Walk

-- Do it together: compose the two witness walks.
@[trans]
theorem reachable_trans {u v w : V} (huv : G.Reachable u v)
    (hvw : G.Reachable v w) : G.Reachable u w := by sorry



-- Exercise: characterize strong connectivity using a hub.
lemma preconnected_iff_exists_forall_reachable (hne : G.vertexSet.Nonempty) :
    G.PreConnected ↔
      ∃ r ∈ G.vertexSet, ∀ v ∈ G.vertexSet,
        G.Reachable r v ∧ G.Reachable v r := by
  constructor
  · intro hG
    obtain ⟨r, hr⟩ := hne
    refine ⟨r, hr, ?_⟩
    sorry
  · rintro ⟨r, hr, h⟩ u hu v hv
    -- Travel from u to r, then from r to v.
    sorry

-- Exercise: unfold the definition; quantify only over actual vertices.
lemma preconnected_iff_forall_reachable :
    G.PreConnected ↔
      ∀ u ∈ G.vertexSet, ∀ v ∈ G.vertexSet, G.Reachable u v := by
  sorry

/-- Challenge exercise: choose a shortest walk and show that it has no
repeated vertices. There are at most `n-1` vertices to visit. -/
lemma exists_central_vertex_if_connected {n : ℕ}
    (G : SimpleDiGraph (Fin n)) (hne : G.vertexSet.Nonempty) (hG : G.PreConnected) :
    ∃ v ∈ G.vertexSet, ∀ w ∈ G.vertexSet,
      ∃ p : G.Walk v w, p.length ≤ n - 1 := by
  sorry


end SimpleDiGraph
