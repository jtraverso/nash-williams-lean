/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassLedgerAssemblyStage75
public import PartitionedTriangleAbsorption.FourClassBudgetStage75
public import PartitionedTriangleAbsorption.FourClassPerturbedAbsorberStage75

/-! # Complete-host assembly with a constructed universal absorber

Only the neutral anti-edgeful reserve remains a geometric input here. The
absorber, fractional repair, main packing and cover-down are constructed.
Original defects are included in the absorber's forbidden set. Taking F empty
recovers the undeleted host. The theorem does not supply the neutral reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassConstructedAssemblyStage75

open Finset TypedLoadNecessity FourClassCopyAdapterStage74 FourClassBudgetStage75

/-- Complete four-class host with sparse original defects. The same neutral
reserve feeds the constructed absorber, exact seed, nibble and cover-down.
All scalar choices and thresholds precede the host and its defect set. -/
theorem perturbed_host_from_neutral_reserve (gamma C alpha : ℝ)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hC : 1 ≤ C)
    (halpha : 0 < alpha) (halpha1 : alpha ≤ 1) :
    ∃ rho eps : ℝ, 0 < rho ∧ 0 < eps ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 4) (G0 : SimpleGraph V) [DecidableRel G0.Adj]
          (F X : Finset (Sym2 V)) [DecidableRel (ReserveCoverDown.reserveGraph X).Adj]
          (phi : Finset V → ℝ),
          (∀ u v, G0.Adj u v ↔ p u ≠ p v) →
          (∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ)) →
          F ⊆ G0.edgeFinset → DegBounded F (rho * Fintype.card V) →
          IsIntDiv p TypedApplicationLinks.F3
            (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset →
          X ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset →
          DegBounded X (rho * Fintype.card V) →
          (∀ l : Fin 4 → Fin 4 → ℤ, Annihilates TypedApplicationLinks.F3 l →
            ∑ e ∈ X, (pairFun l (pairVec p e) : ℝ) = 0) →
          AntiEdgeful p TypedApplicationLinks.F3 (ReserveCoverDown.reserveGraph X) alpha →
          IsRegularAlmostPacking p TypedApplicationLinks.F3
            (G0.deleteEdges (F : Set (Sym2 V))) C eps phi →
          HasDecomp p TypedApplicationLinks.F3
            (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset := by
  obtain ⟨hz,he⟩ := tolerances_positive gamma C hg hC
  obtain ⟨delta,lam,rho0,hd,_,hr,hdelta,N0,hN0⟩ :=
    FourClassPerturbedAbsorberStage75.absorber_avoiding_original_defects gamma
      (deletionTolerance gamma C / 2) hg hg1 (by positivity)
  obtain ⟨N1,hN1⟩ := FourClassLedgerAssemblyStage75.decomposition_from_neutral_ledger
    C alpha hC halpha halpha1
  let rho := min rho0 (deletionTolerance gamma C)
  have hrho : 0 < rho := lt_min hr hz
  have hrhotol : rho ≤ deletionTolerance gamma C := min_le_right _ _
  refine ⟨rho, seedTolerance gamma C, hrho, he, max N0 N1, ?_⟩
  intro V _ _ hV p G0 _ F X _ phi hG0 hsize hF hFd hdiv hXG hXd hX hres hseed
  classical
  have hsize' : ∀ i, gamma * Fintype.card V ≤
      ((ClassRepresentativesStage65.classSet p i).card : ℝ) := by
    intro i
    simpa only [FourClassCopyAdapterStage74.Class, Fintype.card_subtype,
      ClassRepresentativesStage65.classSet]
      using hsize i
  have hFX : DegBounded (F ∪ X) (2 * rho0 * Fintype.card V) := by
    have h := SparseDeletionDegree.degBounded_union hFd hXd
    intro v
    apply (h v).trans
    have hh := mul_le_mul_of_nonneg_right (min_le_left rho0
      (deletionTolerance gamma C)) (Nat.cast_nonneg (Fintype.card V))
    change rho * Fintype.card V + rho * Fintype.card V ≤ 2 * rho0 * Fintype.card V
    dsimp [rho]
    linarith
  obtain ⟨A,hAG,hAX,_,hAd,habs⟩ :=
    hN0 V (le_of_max_le_left hV) p G0 F X hG0 hsize' hF hXG hFX
  have hbudget := compatible_budget gamma C (seedTolerance gamma C) rho (2 * delta)
    rho hg hC le_rfl hrhotol (by linarith) hrhotol
  exact hN1 V (le_of_max_le_right hV) p G0 F A X gamma (seedTolerance gamma C)
    rho (2 * delta) rho phi hG0 hg he.le hrho.le (by positivity) hrho.le
    hsize hAG hXG hAX hdiv habs hX hres hFd hAd hXd hbudget.1 hbudget.2 hseed

end PartitionedTriangleAbsorption.FourClassConstructedAssemblyStage75
