/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Physical opposite-edge transport

The vertices are actual unordered edges, not arbitrary pairs. Adjacency is
exactly opposition inside a physical K4. Both spokes propagate along a walk
in a common link; no universal neighbor of the entire host is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.OppositeEdgeTransportStage259

open Finset

variable {V : Type*} [DecidableEq V]

/-- The opposite-edge graph on the real edges of G. -/
def oppositeEdgeGraph (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e f := Disjoint e.val.toFinset f.val.toFinset ∧
    ∀ x ∈ e.val.toFinset, ∀ y ∈ f.val.toFinset, G.Adj x y
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun _ hx _ hy => (h.2 _ hy _ hx).symm⟩⟩
  loopless := ⟨fun e h => Finset.ne_empty_of_mem (Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e.val))
    (disjoint_self.mp h.1)⟩

/-- The actual unordered edge associated to an adjacency proof. -/
def edge (G : SimpleGraph V) {u v : V} (h : G.Adj u v) : G.edgeSet :=
  ⟨s(u, v), h⟩

/-- The four cross-adjacencies certify that two physical edges are opposite. -/
theorem opposite_adj (G : SimpleGraph V) {u v a b : V}
    (huv : G.Adj u v) (hab : G.Adj a b)
    (hua : G.Adj u a) (hub : G.Adj u b) (hva : G.Adj v a) (hvb : G.Adj v b) :
    (oppositeEdgeGraph G).Adj (edge G huv) (edge G hab) := by
  have hc : ∀ x ∈ (edge G huv).val.toFinset,
      ∀ y ∈ (edge G hab).val.toFinset, G.Adj x y := by
    intro x hx y hy
    simp only [edge, Sym2.toFinset_mk_eq, mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> assumption
  refine ⟨?_, hc⟩
  rw [disjoint_left]
  intro x hx hy
  exact G.irrefl (hc x hx x hy)

/-- Propagate both spokes from a to b along the common link of an edge uv. -/
theorem propagate_spokes (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    {a b : G.commonNeighbors u v}
    (hp : (G.induce (G.commonNeighbors u v)).Reachable a b) (e : G.edgeSet)
    (ha : (oppositeEdgeGraph G).Reachable e (edge G a.property.1))
    (ha' : (oppositeEdgeGraph G).Reachable e (edge G a.property.2)) :
    (oppositeEdgeGraph G).Reachable e (edge G b.property.1) ∧
      (oppositeEdgeGraph G).Reachable e (edge G b.property.2) := by
  obtain ⟨p⟩ := hp
  induction p with
  | nil => exact ⟨ha, ha'⟩
  | @cons x y z hxy p ih =>
    apply ih
    · exact ha'.trans (opposite_adj G x.property.2 y.property.1
        huv.symm y.property.2 x.property.1.symm hxy).reachable
    · exact ha.trans (opposite_adj G x.property.1 y.property.2
        huv y.property.1 x.property.2.symm hxy).reachable

end PartitionedTriangleAbsorption.OppositeEdgeTransportStage259
