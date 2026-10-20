/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.FlexibleConsumer
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedBridge
public import PartitionedTriangleAbsorption.BlowupB.KeevashReserve

@[expose] public section

/-! The existing typed interface follows from the proved real inverse and a
flexible geometric family certificate. KeevashTypedSpec is the CONCLUSION,
not an external existence premise. This bridge does not construct hU. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB
open PartitionedTriangleAbsorption.BlowupB.Flex
open PaddedInputs

theorem keevashTypedSpec_of_flexible_absorber
    (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (hU : UniversalCertFlex F) : KeevashTypedSpec F := by
  intro γ _hγ
  refine ⟨2^21, 1, by norm_num, ?_⟩
  intro ω hω hω1
  obtain ⟨δ₀, hδ₀, hall⟩ := decomposition_of_flexible_absorber F hF hU ω hω hω1
  obtain ⟨ρ, ε, N, _hρ, _hρ1, hε, hdec⟩ := hall δ₀ hδ₀ le_rfl
  refine ⟨ε, hε, N, ?_⟩
  intro V _ _ p J hN _hclasses hloop hallowed hreg hcn hdiv
  classical
  letI : Fintype (edgeGraph J).edgeSet := (edgeGraph J).fintypeEdgeSet
  have hJ : (edgeGraph J).edgeFinset = J := edgeGraph_edges J hloop
  have hs : GuardedSupply p (edgeGraph J) (fun i j => ∃ k, Link F i j k)
      (2^21) (ω * Fintype.card V) := by
    intro S hS i hguard
    have hc := hcn S S i hS (Subset.refl _) (fun u hu =>
      (allowedPair_iff_link F _ _).mpr (hguard u hu))
    refine hc.trans ?_
    exact_mod_cast card_le_card (show
      (univ.filter fun v => p v = i ∧ v ∉ S ∧ ∀ a ∈ S, s(a,v) ∈ J) ⊆
        guardedNeighbours p (edgeGraph J) S i from by
      intro v hv
      obtain ⟨_, hvi, hvS, hvadj⟩ := mem_filter.mp hv
      refine mem_filter.mpr ⟨mem_univ _, hvi, ?_⟩
      intro a ha
      change s(a,v) ∈ J ∧ a ≠ v
      exact ⟨hvadj a ha, fun hav => hvS (hav ▸ ha)⟩)
  obtain ⟨φ, hw, hload⟩ := hreg
  have hweights : ∀ T, IsCopy p F (edgeGraph J) T →
      ω^2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27/ω) / Fintype.card V := by
    intro T hT
    have ht := hw T (PaddedNibble.TypedNibble.isTypedTri_of_isCopy hT)
      (by simpa only [hJ] using PaddedNibble.TypedNibble.triEdges_subset_of_isCopy hT)
    constructor
    · exact (div_le_div_of_nonneg_right
        (pow_le_of_le_one hω.le hω1 (by norm_num : (2:ℕ) ≠ 0))
        (Nat.cast_nonneg _)).trans ht.1
    · refine ht.2.trans ?_
      rw [div_div]
      exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hloads : ∀ e ∈ (edgeGraph J).edgeFinset,
      |(∑ T ∈ copies p F (edgeGraph J) with e ∈ triEdges T, φ T) - 1| ≤ ε := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : (edgeGraph J).Adj u v :=
        (edgeGraph J).mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp he)
      rw [sum_copies_through p F (edgeGraph J) φ huv, hJ]
      exact hload u v (hJ ▸ he)
  have result := hdec V hN p (edgeGraph J) (edgeGraph_allowed p F J hallowed)
    hs (by simpa only [hJ] using hdiv) φ hweights hloads
  simpa only [hJ] using result

#print axioms keevashTypedSpec_of_flexible_absorber

end PaddedGeneral.RealInverse
