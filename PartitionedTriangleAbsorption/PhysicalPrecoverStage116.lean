/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.LoadControlledCoverStage116
public import PartitionedTriangleAbsorption.PairReserveStage116
public import PartitionedTriangleAbsorption.PairReserveBudgetStage116
public import PartitionedTriangleAbsorption.ReturnedDivisibility

/-! # A physical pre-cover preserving the actual parent's divisibility

`W` is the auxiliary region. For an internal recut, take `W` outside the
child. `G` is the available spoke graph, already excluding protected edges.
Only its raw two-root supply is assumed; the sparse reserve and packing
are both constructed. This is not a multiscale supply theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalPrecoverStage116

open Finset TypedApplicationLinks AntiEdgeSelection CoverDownStage105

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_precover (p : V → Fin 4) (E H B : Finset (Sym2 V))
    (hcross : ∀ x y, s(x, y) ∈ E → p x ≠ p y)
    (hdiv : IsIntDiv p F3 E) (W : Finset V)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGE : G.edgeFinset ⊆ E) (hHE : H ⊆ E)
    (hGW : ∀ e ∈ G.edgeFinset, IsSpoke W e)
    (hHW : ∀ x y, s(x, y) ∈ H → x ∉ W ∧ y ∉ W)
    (hGB : Disjoint G.edgeFinset B) (hHB : Disjoint H B)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hrich : ∀ x y, s(x, y) ∈ H →
      β * Fintype.card V ≤ (PairReserveStage116.neighbours W G x y).card)
    (hsize : 96 ≤ β ^ 3 * ρ ^ 12 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V)
    (h a q : ℕ) (hq : 0 < q)
    (hdegH : ∀ x, x ∉ W → incidentLoad H x ≤ h)
    (ha : (a : ℝ) ≤ β * ρ ^ 2 / 2 * Fintype.card V)
    (hbudget : 2 * h + H.card / q < a) :
    ∃ R ⊆ G.edgeFinset, DegBounded R (2 * ρ * Fintype.card V) ∧
      ∃ S ⊆ R, HasDecomp p F3 (H ∪ S) ∧ Disjoint (H ∪ S) B ∧
        (∀ x, x ∉ W → incidentLoad S x = incidentLoad H x) ∧
        (∀ z ∈ W, incidentLoad S z ≤ 2 * q) ∧
        IsIntDiv p F3 (E \ (H ∪ S)) := by
  have hb := (PairReserveBudgetStage116.failure_budget (Fintype.card V) β ρ
    hn.le hβ.le hsize hdegrees).trans_lt (by norm_num : (3 : ℝ) / 4 < 1)
  obtain ⟨R, hR, hdR, hrR⟩ := PairReserveStage116.exists_reserve W H G β ρ
    hβ hρ hρ1 hn hrich hb
  have hr : ∀ x y, s(x, y) ∈ H →
      a ≤ (W.filter fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R).card := by
    intro x y hxy
    have hc : a ≤
        (PairReserveStage116.neighbours W (ReserveCoverDown.reserveGraph R) x y).card := by
      exact_mod_cast ha.trans (hrR x y hxy)
    apply hc.trans (card_le_card ?_)
    intro z hz
    obtain ⟨hzW, hxz, hyz⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hzW, ((SimpleGraph.fromEdgeSet_adj _).mp hxz).1,
      ((SimpleGraph.fromEdgeSet_adj _).mp hyz).1⟩
  obtain ⟨S, hS, hdS, hrS, haS⟩ := LoadControlledCoverStage116.exists_cover
    p E hcross W H R h a q hq hHE (hR.trans hGE) hHW
    (fun e he => hGW e (hR he)) hdegH hr hbudget
  have hSE : S ⊆ E := hS.trans (hR.trans hGE)
  have hav : Disjoint (H ∪ S) B := disjoint_union_left.mpr
    ⟨hHB, hGB.mono_left (hS.trans hR)⟩
  exact ⟨R, hR, hdR, S, hS, hdS, hav, hrS, haS,
    isIntDiv_sdiff_of_hasDecomp hdiv hdS (union_subset hHE hSE)⟩

end PartitionedTriangleAbsorption.PhysicalPrecoverStage116
