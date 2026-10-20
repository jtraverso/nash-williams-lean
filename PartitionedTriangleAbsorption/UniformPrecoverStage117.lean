/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PairSupplyDeletionStage117

/-! # One pre-cover reserve selected before the residual is known

The reserve answers every base query in `J`. Only afterwards is `H` chosen.
Different residuals may use different packings in the same reserve: this
does not assert simultaneous absorption or multiscale iteration.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniformPrecoverStage117

open Finset TypedApplicationLinks AntiEdgeSelection CoverDownStage105

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_reserve_for_all_residuals (p : V → Fin 4)
    (E J B : Finset (Sym2 V)) (W : Finset V)
    (hcross : ∀ x y, s(x, y) ∈ E → p x ≠ p y)
    (hdiv : IsIntDiv p F3 E) (hJE : J ⊆ E)
    (hJW : ∀ x y, s(x, y) ∈ J → x ∉ W ∧ y ∉ W)
    (hJB : Disjoint J B) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hGE : G.edgeFinset ⊆ E) (hGW : ∀ e ∈ G.edgeFinset, IsSpoke W e)
    (β δ ρ : ℝ) (hd : DegBounded B (δ * Fintype.card V))
    (hβ : 0 < β - 2 * δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hrich : ∀ x y, s(x, y) ∈ J →
      β * Fintype.card V ≤ (PairReserveStage116.neighbours W G x y).card)
    (hsize : 96 ≤ (β - 2 * δ) ^ 3 * ρ ^ 12 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V)
    (h a q M : ℕ) (hq : 0 < q)
    (ha : (a : ℝ) ≤ (β - 2 * δ) * ρ ^ 2 / 2 * Fintype.card V)
    (hbudget : 2 * h + M / q < a) :
    ∃ R ⊆ G.edgeFinset, Disjoint R B ∧ DegBounded R (2 * ρ * Fintype.card V) ∧
      ∀ H ⊆ J, H.card ≤ M → (∀ x, x ∉ W → incidentLoad H x ≤ h) →
        ∃ S ⊆ R, HasDecomp p F3 (H ∪ S) ∧ Disjoint (H ∪ S) B ∧
          (∀ x, x ∉ W → incidentLoad S x = incidentLoad H x) ∧
          (∀ z ∈ W, incidentLoad S z ≤ 2 * q) ∧
          IsIntDiv p F3 (E \ (H ∪ S)) := by
  obtain ⟨R, hRG, hRB, hdR, hrR⟩ := PairSupplyDeletionStage117.exists_reserve_avoiding
    W J B G β δ ρ hd hβ hρ hρ1 hn hrich hsize hdegrees
  refine ⟨R, hRG, hRB, hdR, ?_⟩
  intro H hHJ hM hdeg
  have hrH : ∀ x y, s(x, y) ∈ H →
      a ≤ (W.filter fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R).card := by
    intro x y hxy
    have hc : a ≤ (PairReserveStage116.neighbours W
        (ReserveCoverDown.reserveGraph R) x y).card := by
      exact_mod_cast ha.trans (hrR x y (hHJ hxy))
    apply hc.trans (card_le_card ?_)
    intro z hz
    obtain ⟨hzW, hxz, hyz⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨hzW, ((SimpleGraph.fromEdgeSet_adj _).mp hxz).1,
      ((SimpleGraph.fromEdgeSet_adj _).mp hyz).1⟩
  have hbudgetH : 2 * h + H.card / q < a :=
    (Nat.add_le_add_left (Nat.div_le_div_right hM) _).trans_lt hbudget
  obtain ⟨S, hS, hdS, hrS, haS⟩ := LoadControlledCoverStage116.exists_cover
    p E hcross W H R h a q hq (hHJ.trans hJE) (hRG.trans hGE)
    (fun x y hxy => hJW x y (hHJ hxy)) (fun e he => hGW e (hRG he))
    hdeg hrH hbudgetH
  have hSE : S ⊆ E := hS.trans (hRG.trans hGE)
  have hav : Disjoint (H ∪ S) B := disjoint_union_left.mpr
    ⟨hJB.mono_left hHJ, hRB.mono_left hS⟩
  exact ⟨S, hS, hdS, hav, hrS, haS,
    isIntDiv_sdiff_of_hasDecomp hdiv hdS (union_subset (hHJ.trans hJE) hSE)⟩

end PartitionedTriangleAbsorption.UniformPrecoverStage117
