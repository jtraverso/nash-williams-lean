/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.LocalInverseBound

/-! Repair after deleting a decomposable reserve with explicit family-dependent
budgets. The producer and the final choice of the global pipeline thresholds
remain separate. No fixed numerical inverse constant is assumed. -/
namespace PaddedGeneral
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PaddedF12 PaddedF12.PaddedThresholds KeevashQuantitative

theorem hostRepair_local_bound (F : Finset (Multiset (Fin 4)))
    (C : ℝ) (hC : 0 ≤ C) (hI : CompleteInverseCertLocalBound F C)
    (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (ω ε κ : ℝ) (φ : Finset V → ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hε : 0 ≤ ε) (hlarge : 8 ≤ ω * Fintype.card V)
    (hallowed : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 (ω * Fintype.card V))
    (hdiv : IsIntDiv p F G.edgeFinset)
    (hBG : B ⊆ G.edgeFinset) (hBdec : HasDecomp p F B)
    (hBdeg : DegBounded B (κ * Fintype.card V))
    (hw : ∀ T, IsCopy p F G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε)
    (hεbudget : (hostInverseConstant C / ω ^ 9) * ε ≤ ω ^ 2 / 4)
    (hκ : 0 ≤ κ) (hκcap : κ ≤ ω / 8)
    (hκbudget : (hostInverseConstant C / ω ^ 9) * (2 * (27 / ω) * κ) ≤ ω ^ 2 / 4) :
    ∃ ψ : Finset V → ℝ,
      (∀ T, IsCopy p F (G.deleteEdges (B : Set (Sym2 V))) T →
        0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
      ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        (∑ T ∈ copies p F (G.deleteEdges (B : Set (Sym2 V))) with e ∈ triEdges T, ψ T) = 1 := by
  classical
  let H := G.deleteEdges (B : Set (Sym2 V))
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hguardH : GuardedSupply p H (fun i j => ∃ k, Link F i j k) 4
      (ω * Fintype.card V / 2) := by
    have hdelete := guardedSupply_deleteEdges p G (fun i j => ∃ k, Link F i j k)
      4 (ω * Fintype.card V) (κ * Fintype.card V) hs B hBdeg (by positivity)
    apply hdelete.mono le_rfl
    have hb := mul_le_mul_of_nonneg_right hκcap hnR.le
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i := by
    intro i
    simpa only [classSize, classVertices] using hs.class_card i
  have hdivH : IsIntDiv p F H.edgeFinset := by
    rw [show H.edgeFinset = G.edgeFinset \ B from SimpleGraph.edgeFinset_deleteEdges _]
    exact isIntDiv_sdiff_of_hasDecomp hdiv hBdec hBG
  have hw0 : ∀ T, IsCopy p F G T → 0 ≤ φ T ∧
      φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  let θ : ℝ := ε + 2 * (27 / ω) * κ
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hloadH : ∀ e ∈ H.edgeFinset,
      |(∑ T ∈ copies p F H with e ∈ triEdges T, φ T) - 1| ≤ θ := by
    have hr := nearLoads_deleteEdges p F G B (27 / ω) ε
      (κ * Fintype.card V) (by positivity) hn hBdeg φ hw0 hload
    have heq : ε + 2 * (27 / ω) * (κ * Fintype.card V) / Fintype.card V = θ := by
      dsimp only [θ]
      field_simp
    rwa [heq] at hr
  have hactive : H ≤ activeCompleteGraph p F := by
    intro a b hab
    exact ⟨hab.ne, hallowed a b (hHG hab)⟩
  obtain ⟨w, hws, hwe, hwb⟩ := exists_host_chain_inverse_local_bound F C hC hI p H
    (loadDefect p F H φ) θ ω hθ hω hω1 hlarge hmin hguardH
    (loadDefect_supported p F H φ hactive)
    (loadDefect_zero p F H φ)
    (loadDefect_bound p F H φ θ hθ (by
      intro e he
      rw [abs_sub_comm]
      exact hloadH e he))
    (loadDefect_fullSpan p F H φ hdivH)
  apply exactWeights_of_bounded_correction p F H ω hω hω1 hn φ w
    (fun T hT => hw T ⟨hT.1.mono hHG, hT.2⟩) hws
  · intro T hT
    exact (hwb T hT).trans (correction_budget (hostInverseConstant C / ω ^ 9)
      ε (27 / ω) (κ) ω (Fintype.card V) hnR.le hεbudget hκbudget)
  · intro e he
    rw [hwe]
    simp only [loadDefect, he, ite_true]

#print axioms hostRepair_local_bound
end PaddedGeneral

