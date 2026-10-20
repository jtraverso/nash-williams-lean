/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SpokeRecutStage133
public import PartitionedTriangleAbsorption.PairSupplyDeletionStage117

/-! # Stage134: the first spoke reserve, constructed with its balance debt paid

The first spoke reserve `R1` is produced from the actual graph by the existing
Stage117 random reserve (`exists_reserve_avoiding`), applied to the subgraph of
spokes of the child `U`. Its two-root richness for every outer edge, its
maximum degree and its disjointness from a prescribed forbidden set are
inherited from Stage117. The new facts are:

* `R1` consists of spokes of `U`, hence avoids every inner edge of `U`;
* its type-balance discrepancy is bounded crudely by its cardinality, and
  the cardinality of a spoke set is at most `|U|` times its maximum degree.

So `|bal_k(R1)| ≤ 2 ρ n |U|`; no extra probabilistic balance theorem is used.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SpokeReserveStage134

open Finset AntiEdgeSelection CoverDownStage105 TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

theorem balTab_abs_le (k : Fin 2) (i j : Fin 4) : |balTab k i j| ≤ 1 := by
  revert k i j; decide

omit [DecidableEq V] in
theorem balEdge_abs_le (p : V → Fin 4) (k : Fin 2) (e : Sym2 V) :
    |balEdge p k e| ≤ 1 := by
  induction e using Sym2.ind with
  | _ a b => exact balTab_abs_le k (p a) (p b)

omit [DecidableEq V] in
/-- The crude balance bound: every edge contributes at most one. -/
theorem abs_bal_le_card (p : V → Fin 4) (k : Fin 2) (E : Finset (Sym2 V)) :
    |bal p k E| ≤ E.card := by
  unfold bal
  calc |∑ e ∈ E, balEdge p k e| ≤ ∑ e ∈ E, |balEdge p k e| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ E, (1 : ℤ) := sum_le_sum fun e _ => balEdge_abs_le p k e
    _ = E.card := by simp

/-- A spoke set is counted by the loads of its inner endpoints. -/
theorem card_le_sum_loads (U : Finset V) (R : Finset (Sym2 V))
    (hR : ∀ e ∈ R, IsSpoke U e) :
    R.card ≤ ∑ w ∈ U, incidentLoad R w := by
  have hsub : R ⊆ U.biUnion fun w => R.filter fun e => w ∈ e := by
    intro e he
    obtain ⟨a, b, -, hb, rfl⟩ := hR e he
    exact mem_biUnion.mpr ⟨b, hb, mem_filter.mpr ⟨he, Sym2.mem_mk_right a b⟩⟩
  exact (card_le_card hsub).trans card_biUnion_le

/-- The balance debt of a spoke reserve of maximum degree at most `d`. -/
theorem spoke_balance_debt (p : V → Fin 4) (U : Finset V) (R : Finset (Sym2 V)) (d : ℝ)
    (hR : ∀ e ∈ R, IsSpoke U e) (hd : DegBounded R d) :
    ∀ k : Fin 2, |(bal p k R : ℝ)| ≤ U.card * d := by
  intro k
  have h1 : |(bal p k R : ℝ)| ≤ R.card := by
    rw [← Int.cast_abs]; exact_mod_cast abs_bal_le_card p k R
  have h2 : (R.card : ℝ) ≤ ∑ w ∈ U, (incidentLoad R w : ℝ) := by
    exact_mod_cast card_le_sum_loads U R hR
  have h3 : ∑ w ∈ U, (incidentLoad R w : ℝ) ≤ ∑ _w ∈ U, d :=
    sum_le_sum fun w _ => hd w
  rw [sum_const, nsmul_eq_mul] at h3
  linarith

variable [Fintype V]

/-- The non-spoke edges of `G`: these are deleted to obtain the spoke graph. -/
noncomputable def nonSpokes (U : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter fun e => ¬ IsSpoke U e

/-- The spoke subgraph of `G` with respect to `U`. -/
noncomputable abbrev spokeGraph (U : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj] :
    SimpleGraph V :=
  G.deleteEdges (↑(nonSpokes U G) : Set (Sym2 V))

theorem spoke_of_mem (U : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (he : e ∈ (spokeGraph U G).edgeFinset) : IsSpoke U e ∧ e ∈ G.edgeFinset := by
  classical
  rw [SimpleGraph.edgeFinset_deleteEdges] at he
  obtain ⟨heG, hn⟩ := mem_sdiff.mp he
  refine ⟨?_, heG⟩
  by_contra hs
  exact hn (by simp only [nonSpokes, mem_filter]; exact ⟨heG, hs⟩)

omit [DecidableEq V] in
theorem spoke_adj (U : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (x z : V) (hx : x ∉ U) (hz : z ∈ U) (h : G.Adj x z) : (spokeGraph U G).Adj x z := by
  classical
  rw [SimpleGraph.deleteEdges_adj]
  refine ⟨h, ?_⟩
  intro hm
  have hm' : s(x, z) ∈ nonSpokes U G := hm
  simp only [nonSpokes, mem_filter] at hm'
  exact hm'.2 ⟨x, z, hx, hz, rfl⟩

/-- **The first spoke reserve.** From two-root richness of the actual graph
(in the zone `U`, for every outer edge), produce `R1` of actual spokes of `U`,
avoiding the forbidden set `B`, of maximum degree `2ρn`, still two-root rich
for every outer edge, and with balance discrepancy at most `|U| · 2ρn`. -/
theorem exists_first_spoke_reserve (p : V → Fin 4) (U : Finset V) (B : Finset (Sym2 V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (β δ ρ : ℝ)
    (hd : DegBounded B (δ * Fintype.card V))
    (hβ : 0 < β - 2 * δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hrich : ∀ x y, s(x, y) ∈ G.edgeFinset → x ∉ U → y ∉ U →
      β * Fintype.card V ≤ (U.filter fun z => G.Adj x z ∧ G.Adj y z).card)
    (hsize : 96 ≤ (β - 2 * δ) ^ 3 * ρ ^ 12 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V) :
    ∃ R1 ⊆ G.edgeFinset, (∀ e ∈ R1, IsSpoke U e) ∧ Disjoint R1 B ∧
      DegBounded R1 (2 * ρ * Fintype.card V) ∧
      (∀ x y, s(x, y) ∈ G.edgeFinset → x ∉ U → y ∉ U →
        (β - 2 * δ) * ρ ^ 2 / 2 * Fintype.card V ≤
          ((U.filter fun w => s(x, w) ∈ R1 ∧ s(y, w) ∈ R1).card : ℝ)) ∧
      ∀ k : Fin 2, |(bal p k R1 : ℝ)| ≤ U.card * (2 * ρ * Fintype.card V) := by
  classical
  let J : Finset (Sym2 V) := G.edgeFinset.filter fun e => ∀ v ∈ e, v ∉ U
  have hJ : ∀ x y, s(x, y) ∈ J → s(x, y) ∈ G.edgeFinset ∧ x ∉ U ∧ y ∉ U := by
    intro x y h
    obtain ⟨hG, hout⟩ := mem_filter.mp h
    exact ⟨hG, hout x (Sym2.mem_mk_left x y), hout y (Sym2.mem_mk_right x y)⟩
  have hrich' : ∀ x y, s(x, y) ∈ J → β * Fintype.card V ≤
      (PairReserveStage116.neighbours U (spokeGraph U G) x y).card := by
    intro x y hxy
    obtain ⟨hG, hx, hy⟩ := hJ x y hxy
    apply (hrich x y hG hx hy).trans
    apply Nat.cast_le.mpr (card_le_card ?_)
    intro z hz
    obtain ⟨hzU, hxz, hyz⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hzU, spoke_adj U G x z hx hzU hxz, spoke_adj U G y z hy hzU hyz⟩
  obtain ⟨R, hRG, hRB, hdR, hrR⟩ := PairSupplyDeletionStage117.exists_reserve_avoiding
    U J B (spokeGraph U G) β δ ρ hd hβ hρ hρ1 hn hrich' hsize hdegrees
  have hspoke : ∀ e ∈ R, IsSpoke U e := fun e he => (spoke_of_mem U G e (hRG he)).1
  refine ⟨R, fun e he => (spoke_of_mem U G e (hRG he)).2, hspoke, hRB, hdR, ?_,
    spoke_balance_debt p U R _ hspoke hdR⟩
  intro x y hG hx hy
  have hmem : s(x, y) ∈ J := mem_filter.mpr ⟨hG, by
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hx
    · exact hy⟩
  apply (hrR x y hmem).trans
  apply Nat.cast_le.mpr (card_le_card ?_)
  intro z hz
  obtain ⟨hzU, hxz, hyz⟩ := mem_filter.mp hz
  exact mem_filter.mpr ⟨hzU, ((SimpleGraph.fromEdgeSet_adj _).mp hxz).1,
    ((SimpleGraph.fromEdgeSet_adj _).mp hyz).1⟩

end PartitionedTriangleAbsorption.SpokeReserveStage134
