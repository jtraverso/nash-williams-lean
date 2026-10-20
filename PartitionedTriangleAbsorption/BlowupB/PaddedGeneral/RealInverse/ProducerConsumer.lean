/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.TypedConsumer
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Target

/-! Direct assembly of an existential universal-absorber producer with the
proved real-inverse pipeline. No flexible-certificate conversion is assumed.
The producer's reserve density is reduced, never enlarged. All parameters
and the maximum of the two order thresholds are fixed before the host. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB
open PartitionedTriangleAbsorption.BlowupB.UniversalProducer
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PaddedF12 KeevashQuantitative PaddedInputs

theorem decomposition_of_producer
    (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (S : ℕ) (hS : 4 ≤ S) (hP : ProducerTarget F S)
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) →
        GuardedSupply p G (fun i j => ∃ k, Link F i j k) S (ω * Fintype.card V) →
        IsIntDiv p F G.edgeFinset → ∀ φ : Finset V → ℝ,
        (∀ T, IsCopy p F G T →
          ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V) →
        (∀ e ∈ G.edgeFinset,
          |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) →
        HasDecomp p F G.edgeFinset := by
  set C := generalInverseConstant F hF.card_three
  have hC : 0 ≤ C := (generalInverseConstant_pos F hF.card_three).le
  set κ := inverseKappa C ω
  have hκ : 0 < κ := (inverse_scales_pos hC hω).1
  have hκω : κ ≤ ω / 8 := min_le_left _ _
  obtain ⟨ρ₀, hρ₀, N₀, hprod⟩ := hP ω hω hω1 (κ / 8) (by positivity)
  set ρ := min ρ₀ (κ / 8)
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρsmall : ρ ≤ κ / 8 := min_le_right _ _
  have hρ1 : ρ ≤ 1 := by linarith
  set ε := min (inverseEpsilon C ω)
    (loadTolerance (min (ω / 8) (min 1 (ω ^ 2)))) / 2
  have hmin : 0 < min (inverseEpsilon C ω)
      (loadTolerance (min (ω / 8) (min 1 (ω ^ 2)))) :=
    lt_min (inverse_scales_pos hC hω).2 (initial_loadTolerance_pos hω)
  have hε : 0 < ε := half_pos hmin
  refine ⟨ε, hε, max N₀ (scaledOrder ω ρ), ?_⟩
  intro V _ _ hN p G _ hG hs hdiv φ hw hload
  have hU := universalAbsorbers_mono p F G
    (hprod V p G ((le_max_left _ _).trans hN) hG hs)
    (show ρ ≤ ρ₀ from min_le_left _ _) (le_refl (κ / 8))
  have hnum : ScaledNumericInputs (Fintype.card V) C ω ε ρ (κ / 8) :=
    scaled_numeric_inputs_of_order C ω ε ρ (κ / 8) hC hω hω1 hε.le hρ hρ1
      (by dsimp [ε]; linarith) (by linarith) _ ((le_max_right _ _).trans hN)
  exact decomposition_general F hF ω ε ρ (κ / 8) V hnum p G hU hG
    (hs.mono hS le_rfl) hdiv φ hw hload

/-- The typed interface is derived, not assumed as an external theorem. -/
theorem keevashTypedSpec_of_producer
    (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (S : ℕ) (hS : 4 ≤ S) (hP : ProducerTarget F S) : KeevashTypedSpec F := by
  intro γ _hγ
  refine ⟨S, 1, by norm_num, ?_⟩
  intro ω hω hω1
  obtain ⟨ε, hε, N, hdec⟩ := decomposition_of_producer F hF S hS hP ω hω hω1
  refine ⟨ε, hε, N, ?_⟩
  intro V _ _ p J hN _hclasses hloop hallowed hreg hcn hdiv
  classical
  let : Fintype (edgeGraph J).edgeSet := (edgeGraph J).fintypeEdgeSet
  have hJ : (edgeGraph J).edgeFinset = J := edgeGraph_edges J hloop
  have hs : GuardedSupply p (edgeGraph J) (fun i j => ∃ k, Link F i j k)
      S (ω * Fintype.card V) := by
    intro R hR i hguard
    have hc := hcn R R i hR (Subset.refl _) (fun u hu =>
      (allowedPair_iff_link F _ _).mpr (hguard u hu))
    refine hc.trans ?_
    exact_mod_cast card_le_card (show
      (univ.filter fun v => p v = i ∧ v ∉ R ∧ ∀ a ∈ R, s(a,v) ∈ J) ⊆
        guardedNeighbours p (edgeGraph J) R i from by
      intro v hv
      obtain ⟨_, hvi, hvR, hvadj⟩ := mem_filter.mp hv
      refine mem_filter.mpr ⟨mem_univ _, hvi, ?_⟩
      intro a ha
      change s(a,v) ∈ J ∧ a ≠ v
      exact ⟨hvadj a ha, fun hav => hvR (hav ▸ ha)⟩)
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

#print axioms decomposition_of_producer
#print axioms keevashTypedSpec_of_producer

end PaddedGeneral.RealInverse
