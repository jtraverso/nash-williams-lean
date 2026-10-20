/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.GoodEdgeConnectivityStage261
public import PartitionedTriangleAbsorption.LinkTransportStage259
public import Mathlib.Combinatorics.SimpleGraph.Walks.Maps

/-! Connect a cross edge to the good remainder using one auxiliary for the
whole path. Walk.induce preserves the actual host adjacencies. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open Finset OppositeEdgeTransportStage259

variable {V : Type*} [DecidableEq V]

/-- A path contained in one common link, ending in a triangle, transports
its initial spoke to an edge of that triangle. -/
theorem spoke_to_triangle_along_walk (G : SimpleGraph V) {s a w x y z : V}
    (hsa : G.Adj s a) (p : G.Walk w x)
    (hsupport : ∀ t ∈ p.support, G.Adj s t ∧ G.Adj a t)
    (hy : G.Adj s y ∧ G.Adj a y) (hz : G.Adj s z ∧ G.Adj a z)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    (oppositeEdgeGraph G).Reachable
      (edge G (hsupport w p.start_mem_support).1) (edge G hyz) := by
  let w' : G.commonNeighbors s a := ⟨w, hsupport w p.start_mem_support⟩
  let x' : G.commonNeighbors s a := ⟨x, hsupport x p.end_mem_support⟩
  let y' : G.commonNeighbors s a := ⟨y, hy⟩
  let z' : G.commonNeighbors s a := ⟨z, hz⟩
  have hp : (G.induce (G.commonNeighbors s a)).Reachable x' w' :=
    ⟨(p.induce (G.commonNeighbors s a) hsupport).reverse⟩
  obtain ⟨hx1, hx2⟩ := k5_spokes G hsa (a := x') (b := y') (c := z') hxy hxz hyz
  have hw := propagate_spokes G hsa hp (edge G hsa) hx1 hx2
  exact hw.1.symm.trans (opposite_adj G hsa hyz hy.1 hz.1 hy.2 hz.2).reachable

/-- A good path of length at most 14 needs at most 17 simultaneous roots.
The auxiliary is constructed from the original degree hierarchy. -/
theorem good_path_spoke_reaches_triangle [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + e) * Fintype.card V)
    (u v s w x y z : V) (hsw : G.Adj s w) (p : G.Walk w x)
    (hlen : p.length ≤ 14)
    (hxy : G.Adj x y) (hxz : G.Adj x z) (hyz : G.Adj y z) :
    let S := univ.filter (fun t => G.Adj u t ∧ G.Adj v t)
    let B := univ.filter (fun t => t ∉ S ∧ a * Fintype.card V / 100 <
      ((S.filter (fun r => ¬ G.Adj t r)).card : ℝ))
    let R := univ \ (S ∪ B)
    (∀ t ∈ p.support, t ∈ R ∧ G.Adj s t) →
    (y ∈ R ∧ G.Adj s y) → (z ∈ R ∧ G.Adj s z) →
      (oppositeEdgeGraph G).Reachable (edge G hsw) (edge G hyz) := by
  classical
  intro S B R hpath hy hz
  let Z := p.support.toFinset ∪ {x, y, z}
  have hZ : Z.card ≤ 17 := walk_triangle_support_bound G p y z hlen
  have hgood : Z ⊆ R := by
    intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact (hpath t (List.mem_toFinset.mp ht)).1
    · simp only [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl | rfl
      · exact (hpath _ p.end_mem_support).1
      · exact hy.1
      · exact hz.1
  obtain ⟨aux, _, _, _, hsaux, _, hall⟩ :=
    good_roots_have_common_edge G a e ha ha1 he hn hsmall hdeg u v s Z hZ hgood
  have hsupp : ∀ t ∈ p.support, G.Adj s t ∧ G.Adj aux t := by
    intro t ht
    exact ⟨(hpath t ht).2, (hall t (mem_union_left _ (List.mem_toFinset.mpr ht))).1⟩
  have hay : G.Adj aux y := (hall y (by simp [Z])).1
  have haz : G.Adj aux z := (hall z (by simp [Z])).1
  exact spoke_to_triangle_along_walk G hsaux p hsupp ⟨hy.2, hay⟩ ⟨hz.2, haz⟩ hxy hxz hyz

end PartitionedTriangleAbsorption.GoodRemaindersStage261
