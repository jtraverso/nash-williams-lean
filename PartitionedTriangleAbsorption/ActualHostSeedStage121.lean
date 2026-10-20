/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.JointRecutPrecoverStage121
public import PartitionedTriangleAbsorption.RecutSeedRepairStage119

/-! # Repair the actual host after joint recut and pre-cover

Both balance and the degree of the final deletion are derived from the
physical outputs. The base must still be complete four-partite and the
explicit numerical margin must hold. Unused pre-cover supply is not deleted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ActualHostSeedStage121

open Finset TypedApplicationLinks TypedLoadNecessity FourClassCopyAdapterStage74
  CoverDownStage105 AntiEdgeSelection ReserveAwareRecutStage120 JointRecutPrecoverStage121

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem actual_host_edges (G : SimpleGraph V) [DecidableRel G.Adj]
    (B R J Y S Z : Finset (Sym2 V)) (hZ : Z = B ∪ (S ∪ (R ∪ J))) (hY : Y ⊆ J) :
    (G.deleteEdges Z).edgeFinset =
      (G.deleteEdges B).edgeFinset \ ((Y ∪ S) ∪ (R ∪ (J \ Y))) := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [mem_sdiff, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      SimpleGraph.deleteEdges_adj, mem_coe, hZ, mem_union]
    have := @hY s(u, v)
    tauto

theorem repair_actual_host (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (B R J Y S Z : Finset (Sym2 V)) (hZ : Z = B ∪ (S ∪ (R ∪ J)))
    (hRJ : Disjoint R J) (hY : Y ⊆ J) (hS : Disjoint S (R ∪ J))
    (hsub : S ∪ (R ∪ J) ⊆ (G.deleteEdges B).edgeFinset)
    (hparent : ∀ k : Fin 2, bal p k (G.deleteEdges B).edgeFinset = 0)
    (hcombined : ∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0)
    (hdec : HasDecomp p F3 (Y ∪ S))
    (s r D : ℕ) (hSdeg : ∀ v, incidentLoad S v ≤ s)
    (hRdeg : ∀ v, incidentLoad R v ≤ r) (hJdeg : ∀ v, incidentLoad J v ≤ D)
    (γ C b ρ ε E : ℝ) (hγ : 0 < γ) (hC : 1 ≤ C) (hb : 0 ≤ b)
    (hρ : 0 ≤ ρ) (hε : 0 ≤ ε) (hn : 0 < Fintype.card V)
    (hsmall : 72 * (b + ρ) ≤ γ ^ 3)
    (hsize : ∀ i, γ * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hBd : DegBounded B (b * Fintype.card V))
    (hbudget : ((s + r + D : ℕ) : ℝ) ≤ ρ * Fintype.card V)
    (hmargin : E + 36 * (ε + 4 * C * ρ) / γ ^ 3 ≤ 1 / (2 * C))
    (φ : Finset V → ℝ)
    (hw : ∀ s, IsCopy p F3 (G.deleteEdges B) s →
      (1 / C - E) / Fintype.card V ≤ φ s ∧ φ s ≤ (C + E) / Fintype.card V)
    (hl : ∀ e ∈ (G.deleteEdges B).edgeFinset,
      |1 - edgeLoad p F3 (G.deleteEdges B) φ e| ≤ ε) :
    ∃ ψ : Finset V → ℝ,
      IsRegularAlmostPacking p F3 (G.deleteEdges Z) (2 * C) 0 ψ := by
  classical
  let L := S ∪ (R ∪ J)
  have hLd : DegBounded L (ρ * Fintype.card V) := by
    intro v
    have hh := deletion_degree S R J s r D hSdeg hRdeg hJdeg v
    have hc : (incidentLoad L v : ℝ) ≤ (s + r + D : ℕ) := by
      exact_mod_cast hh
    exact hc.trans hbudget
  have hZd : DegBounded Z ((b + ρ) * Fintype.card V) := by
    rw [hZ]
    simpa only [add_mul] using PairSupplyDeletionStage117.degree_union B L
      (b * Fintype.card V) (ρ * Fintype.card V) hBd hLd
  have hbal : ∀ k : Fin 2, bal p k (G.deleteEdges Z).edgeFinset = 0 := by
    intro k
    rw [actual_host_edges G B R J Y S Z hZ hY,
      actual_host_balance p k (G.deleteEdges B).edgeFinset R J Y S
      hRJ hY hS hsub (hparent k) hdec, hcombined k, neg_zero]
  obtain ⟨ψ, -, -, hψ⟩ := RecutSeedRepairStage119.repair_recut p G hG B L Z
    hZ γ C (b + ρ) ρ ε E hγ hC (add_nonneg hb hρ) hρ hε hn hsmall hsize
    hZd hLd hbal hmargin φ hw hl
  exact ⟨ψ, hψ⟩

end PartitionedTriangleAbsorption.ActualHostSeedStage121
