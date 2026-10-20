/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedAssembly
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.HostInverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.LoadDefect
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.Deletion
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PositiveRepair

@[expose] public section

/-!
# Positive fractional repair after deleting the constructed absorber and reserve

The deleted set is physical, sparse and decomposable. Its complement remains
integrally divisible, and the original weights give a compatible small demand.
The signed inverse is constructed in that same complement. Its coefficient
bound fits inside half the original positive lower weight.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

theorem hostRepair_F12 (kind : Family) : HostRepairSpec kind := by
  intro V _ _ p G _ B ω ε φ hω hω1 hε hlarge hallowed hs hdiv hBG hBdec hBdeg hw hload hεbudget
  classical
  let H := G.deleteEdges (B : Set (Sym2 V))
  have hHG : H ≤ G := SimpleGraph.deleteEdges_le _
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hκ := paddedKappa_pos hω
  have hκcap := PaddedThresholds.kappa_small hω hω1
  have hguardH : GuardedSupply p H (fun i j => ∃ k, Link kind.types i j k) 4
      (ω * Fintype.card V / 2) := by
    have hdelete := guardedSupply_deleteEdges p G (fun i j => ∃ k, Link kind.types i j k)
      4 (ω * Fintype.card V) (paddedKappa ω * Fintype.card V) hs B hBdeg (by positivity)
    apply hdelete.mono le_rfl
    have hb := mul_le_mul_of_nonneg_right hκcap hnR.le
    norm_num only [Nat.cast_ofNat]
    nlinarith
  have hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i := by
    intro i
    simpa only [classSize, classVertices] using hs.class_card i
  have hdivH : IsIntDiv p kind.types H.edgeFinset := by
    rw [show H.edgeFinset = G.edgeFinset \ B from SimpleGraph.edgeFinset_deleteEdges _]
    exact isIntDiv_sdiff_of_hasDecomp hdiv hBdec hBG
  have hw0 : ∀ T, IsCopy p kind.types G T → 0 ≤ φ T ∧
      φ T ≤ (27 / ω) / Fintype.card V := by
    intro T hT
    exact ⟨(by positivity : 0 ≤ ω ^ 2 / (Fintype.card V : ℝ)).trans (hw T hT).1,
      (hw T hT).2⟩
  let θ : ℝ := ε + 2 * (27 / ω) * paddedKappa ω
  have hθ : 0 ≤ θ := by dsimp only [θ]; positivity
  have hloadH : ∀ e ∈ H.edgeFinset,
      |(∑ T ∈ copies p kind.types H with e ∈ triEdges T, φ T) - 1| ≤ θ := by
    have hr := nearLoads_deleteEdges p kind.types G B (27 / ω) ε
      (paddedKappa ω * Fintype.card V) (by positivity) hn hBdeg φ hw0 hload
    have heq : ε + 2 * (27 / ω) * (paddedKappa ω * Fintype.card V) / Fintype.card V = θ := by
      dsimp only [θ]
      field_simp
    rwa [heq] at hr
  have hactive : H ≤ activeCompleteGraph p kind.types := by
    intro a b hab
    exact ⟨hab.ne, hallowed a b (hHG hab)⟩
  have hfamily : kind.types = F1 ∨ kind.types = F2 := by
    cases kind
    · exact Or.inl rfl
    · exact Or.inr rfl
  obtain ⟨w, hws, hwe, hwb⟩ := exists_host_chain_inverse p kind.types H
    (loadDefect p kind.types H φ) θ ω hθ hω hω1 hlarge hmin hguardH
    (loadDefect_supported p kind.types H φ hactive)
    (loadDefect_zero p kind.types H φ)
    (loadDefect_bound p kind.types H φ θ hθ (by
      intro e he
      rw [abs_sub_comm]
      exact hloadH e he))
    (loadDefect_family p kind.types H φ hfamily hdivH)
  apply exactWeights_of_bounded_correction p kind.types H ω hω hω1 hn φ w
    (fun T hT => hw T ⟨hT.1.mono hHG, hT.2⟩) hws
  · intro T hT
    exact (hwb T hT).trans (correction_budget ((2 : ℝ) ^ 32 / ω ^ 9)
      ε (27 / ω) (paddedKappa ω) ω (Fintype.card V) hnR.le hεbudget (padded_repair_budget hω))
  · intro e he
    rw [hwe]
    simp only [loadDefect, he, ite_true]

#print axioms hostRepair_F12

end PaddedF12
