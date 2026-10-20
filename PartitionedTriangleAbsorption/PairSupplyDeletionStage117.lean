/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalPrecoverStage116
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-! # Two-root supply after deleting previously reserved edges

The loss is measured on the actual graph, not only on its label counts.
Deleting a degree-delta edge set costs at most twice delta per query.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairSupplyDeletionStage117

open Finset AntiEdgeSelection CoverDownStage105 PairReserveStage116

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem neighbours_loss (W : Finset V) (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Finset (Sym2 V)) (x y : V) :
    (neighbours W G x y).card ≤
      (neighbours W (G.deleteEdges B) x y).card + incidentLoad B x + incidentLoad B y := by
  let Bad := (W.filter fun z => s(x, z) ∈ B) ∪ (W.filter fun z => s(y, z) ∈ B)
  have hb : Bad.card ≤ incidentLoad B x + incidentLoad B y :=
    (card_union_le _ _).trans (Nat.add_le_add
      (card_spoke_filter_le W B x) (card_spoke_filter_le W B y))
  have hs : neighbours W G x y ⊆ neighbours W (G.deleteEdges B) x y ∪ Bad := by
    intro z hz
    simp only [neighbours, Bad, mem_filter, mem_union,
      SimpleGraph.deleteEdges_adj, mem_coe] at hz ⊢
    tauto
  have hc := (card_le_card hs).trans (card_union_le _ _)
  omega

theorem supply_after_deletion (W : Finset V) (J B : Finset (Sym2 V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (β δ : ℝ)
    (hd : DegBounded B (δ * Fintype.card V))
    (hr : ∀ x y, s(x, y) ∈ J → β * Fintype.card V ≤ (neighbours W G x y).card) :
    ∀ x y, s(x, y) ∈ J → (β - 2 * δ) * Fintype.card V ≤
      (neighbours W (G.deleteEdges B) x y).card := by
  intro x y hxy
  have hc : ((neighbours W G x y).card : ℝ) ≤
      (neighbours W (G.deleteEdges B) x y).card +
        (incidentLoad B x : ℝ) + incidentLoad B y := by
    exact_mod_cast neighbours_loss W G B x y
  have hx : (incidentLoad B x : ℝ) ≤ δ * Fintype.card V := hd x
  have hy : (incidentLoad B y : ℝ) ≤ δ * Fintype.card V := hd y
  have hh := hr x y hxy
  nlinarith

omit [Fintype V] in
theorem degree_union (B R : Finset (Sym2 V)) (b r : ℝ)
    (hB : DegBounded B b) (hR : DegBounded R r) : DegBounded (B ∪ R) (b + r) := by
  intro v
  have hc : (incidentLoad (B ∪ R) v : ℝ) ≤
      (incidentLoad B v : ℝ) + incidentLoad R v := by
    exact_mod_cast incidentLoad_union_le B R v
  exact hc.trans (add_le_add (hB v) (hR v))

theorem exists_reserve_avoiding (W : Finset V) (J B : Finset (Sym2 V))
    (G : SimpleGraph V) [DecidableRel G.Adj] (β δ ρ : ℝ)
    (hd : DegBounded B (δ * Fintype.card V))
    (hβ : 0 < β - 2 * δ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hrich : ∀ x y, s(x, y) ∈ J → β * Fintype.card V ≤ (neighbours W G x y).card)
    (hsize : 96 ≤ (β - 2 * δ) ^ 3 * ρ ^ 12 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V) :
    ∃ R ⊆ G.edgeFinset, Disjoint R B ∧ DegBounded R (2 * ρ * Fintype.card V) ∧
      ∀ x y, s(x, y) ∈ J → (β - 2 * δ) * ρ ^ 2 / 2 * Fintype.card V ≤
        (neighbours W (ReserveCoverDown.reserveGraph R) x y).card := by
  have hr := supply_after_deletion W J B G β δ hd hrich
  have hb := (PairReserveBudgetStage116.failure_budget (Fintype.card V) (β - 2 * δ) ρ
    hn.le hβ.le hsize hdegrees).trans_lt (by norm_num : (3 : ℝ) / 4 < 1)
  obtain ⟨R, hR, hdR, hrR⟩ := PairReserveStage116.exists_reserve W J
    (G.deleteEdges B) (β - 2 * δ) ρ hβ hρ hρ1 hn hr hb
  rw [SimpleGraph.edgeFinset_deleteEdges] at hR
  exact ⟨R, hR.trans sdiff_subset,
    disjoint_left.mpr (fun e he hbe => (mem_sdiff.mp (hR he)).2 hbe), hdR, hrR⟩

end PartitionedTriangleAbsorption.PairSupplyDeletionStage117
