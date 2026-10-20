/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ProducedReserveStage124
public import PartitionedTriangleAbsorption.ActualHostSeedStage121

/-! # Protect a dense core by location, not by a sparse-degree budget

Every core edge has both endpoints in K. Triangles supported outside K and
connectors with an endpoint outside K cannot consume such an edge.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.LateReserveStage125

open Finset TypedApplicationLinks AntiEdgeSelection CoverDownStage105
open ReserveQueryGeometryStage123 ReserveAwareRecutStage120

variable {V : Type*} [DecidableEq V]

/-- Even if the core is dense, its degree is bounded by its vertex count.
This is a repair cost, not a cost charged to reserve placement. -/
theorem core_degree_bound (K : Finset V) (J : Finset (Sym2 V))
    (hJ : ∀ e ∈ J, IsInner K e) (v : V) : incidentLoad J v ≤ K.card := by
  have hsub : J.filter (fun e => v ∈ e) ⊆ K.image (fun w => s(v, w)) := by
    intro e he
    obtain ⟨heJ, hve⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ a b =>
      rcases Sym2.mem_iff.mp hve with h | h
      · subst a
        exact mem_image.mpr ⟨b, hJ _ heJ b (by simp), rfl⟩
      · subst b
        exact mem_image.mpr ⟨a, hJ _ heJ a (by simp), Sym2.eq_swap⟩
  exact (card_le_card hsub).trans (card_image_le)

omit [DecidableEq V] in
theorem edge_not_core (K : Finset V) (J : Finset (Sym2 V))
    (hJ : ∀ e ∈ J, IsInner K e) (u v : V) (hv : v ∉ K) : s(u, v) ∉ J := by
  intro he
  exact hv (hJ _ he v (by simp))

theorem triangle_avoids_core (K : Finset V) (J : Finset (Sym2 V))
    (hJ : ∀ e ∈ J, IsInner K e) (r : V × V × V)
    (ha : r.2.1 ∉ K) (hb : r.2.2 ∉ K) : Disjoint (resTri r) J := by
  apply disjoint_left.mpr
  intro e he hj
  simp only [resTri, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · exact edge_not_core K J hJ _ _ ha hj
  · exact edge_not_core K J hJ _ _ hb hj
  · exact edge_not_core K J hJ _ _ hb hj

omit [DecidableEq V] in
theorem connectors_avoid_core (K : Finset V) (J : Finset (Sym2 V))
    (hJ : ∀ e ∈ J, IsInner K e) (y z : V) (r : V × V × V)
    (ha : r.2.1 ∉ K) (hb : r.2.2 ∉ K) :
    s(y, r.2.1) ∉ J ∧ s(r.2.2, z) ∉ J := by
  refine ⟨edge_not_core K J hJ _ _ ha, ?_⟩
  simpa only [Sym2.eq_swap] using edge_not_core K J hJ z r.2.2 hb

/-- No degree assumption on J is used: even a dense core is protected. -/
theorem reserve_avoids_core (W K : Finset V) (J : Finset (Sym2 V))
    (hWK : Disjoint W K) (hJ : ∀ e ∈ J, IsInner K e)
    (T : Finset (V × V × V)) (hT : ∀ r ∈ T, r.2.1 ∈ W ∧ r.2.2 ∈ W) :
    Disjoint (resEdges T) J := by
  rw [resEdges, disjoint_biUnion_left]
  intro r hr
  exact triangle_avoids_core K J hJ r
    (fun hk => disjoint_left.mp hWK (hT r hr).1 hk)
    (fun hk => disjoint_left.mp hWK (hT r hr).2 hk)

theorem reserve_decomp (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (hT : ∀ r ∈ T, resTri r ⊆ E) : HasDecomp p F3 (resEdges T) :=
  RefinerAssembly.hasDecomp_biUnion T resTri
    (fun r hr => hasDecomp_resTri p E hcross (hT r hr)) hd

/-- Withholding complete triangles cannot introduce a new balance debt. -/
theorem balance_after_reserve (p : V → Fin 4) (H R : Finset (Sym2 V))
    (hR : R ⊆ H) (hdec : HasDecomp p F3 R)
    (hbal : ∀ k : Fin 2, bal p k H = 0) :
    ∀ k : Fin 2, bal p k (H \ R) = 0 := by
  intro k
  rw [bal_sdiff p k hR, hbal k, bal_zero_of_hasDecomp p k hdec, sub_self]

/-- The balanced host consumed below is precisely the output of the
reserve-aware recut and its physical pre-cover, not the untrimmed child. -/
theorem precover_host_balanced (p : V → Fin 4) (E R J Y S : Finset (Sym2 V))
    (hRJ : Disjoint R J) (hY : Y ⊆ J) (hS : Disjoint S (R ∪ J))
    (hsub : S ∪ (R ∪ J) ⊆ E) (hE : ∀ k : Fin 2, bal p k E = 0)
    (hdec : HasDecomp p F3 (Y ∪ S))
    (hrecut : ∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0) :
    ∀ k : Fin 2, bal p k (E \ ((S ∪ R) ∪ J)) = 0 := by
  intro k
  have heq : (Y ∪ S) ∪ (R ∪ (J \ Y)) = (S ∪ R) ∪ J := by
    ext e
    simp only [mem_union, mem_sdiff]
    have := @hY e
    tauto
  have hh := actual_host_balance p k E R J Y S hRJ hY hS hsub (hE k) hdec
  rw [heq, hrecut k, neg_zero] at hh
  exact hh

theorem deleted_edges [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (F D : Finset (Sym2 V)) :
    (G.deleteEdges (F ∪ D)).edgeFinset = (G.deleteEdges F).edgeFinset \ D := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.deleteEdges_adj,
      SimpleGraph.mem_edgeSet, Set.mem_union, mem_coe]
    tauto

end PartitionedTriangleAbsorption.LateReserveStage125
