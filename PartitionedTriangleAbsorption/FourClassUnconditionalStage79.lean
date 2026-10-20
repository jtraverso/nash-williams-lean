/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassConstructedAssemblyStage75
public import PartitionedTriangleAbsorption.NeutralReserveProducerStage78

/-! # Four-class decomposition without supplied geometric intermediates

The absorber capacity is chosen before the reserve's anti-edgeful parameter.
The latter affects only the order threshold of the accepted cover-down. This
ordering avoids a circular choice between reserve density and absorber capacity.
Original integral divisibility and the original bounded almost packing remain
inputs. No reserve, absorber, exact seed or external rounding theorem is supplied.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassUnconditionalStage79

open Finset TypedLoadNecessity FourClassBudgetStage75 ClassRepresentativesStage65

theorem capacity_before_supply (gamma C : ℝ) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (hC : 1 ≤ C) :
    ∃ rho eps : ℝ, 0 < rho ∧ 0 < eps ∧
      ∀ alpha : ℝ, 0 < alpha → alpha ≤ 1 → ∃ N : ℕ,
        ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
          ∀ (p : V → Fin 4) (G0 : SimpleGraph V) [DecidableRel G0.Adj]
            (F X : Finset (Sym2 V)) [DecidableRel (ReserveCoverDown.reserveGraph X).Adj]
            (phi : Finset V → ℝ),
            (∀ u v, G0.Adj u v ↔ p u ≠ p v) →
            (∀ i, gamma * Fintype.card V ≤ ((classSet p i).card : ℝ)) →
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
  let rho := min rho0 (deletionTolerance gamma C)
  have hrho : 0 < rho := lt_min hr hz
  have hrhotol : rho ≤ deletionTolerance gamma C := min_le_right _ _
  refine ⟨rho,seedTolerance gamma C,hrho,he,?_⟩
  intro alpha halpha halpha1
  obtain ⟨N1,hN1⟩ := FourClassLedgerAssemblyStage75.decomposition_from_neutral_ledger
    C alpha hC halpha halpha1
  refine ⟨max N0 N1,?_⟩
  intro V _ _ hV p G0 _ F X _ phi hG0 hsize hF hFd hdiv hXG hXd hX hres hseed
  classical
  have hsize' : ∀ i, gamma * Fintype.card V ≤
      (Fintype.card (FourClassCopyAdapterStage74.Class p i) : ℝ) := by
    intro i
    simpa only [FourClassCopyAdapterStage74.Class,Fintype.card_subtype,classSet]
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
    hN0 V (le_of_max_le_left hV) p G0 F X hG0 hsize hF hXG hFX
  have hbudget := compatible_budget gamma C (seedTolerance gamma C) rho (2 * delta)
    rho hg hC le_rfl hrhotol (by linarith) hrhotol
  exact hN1 V (le_of_max_le_right hV) p G0 F A X gamma (seedTolerance gamma C)
    rho (2 * delta) rho phi hG0 hg he.le hrho.le (by positivity) hrho.le
    hsize' hAG hXG hAX hdiv habs hX hres hFd hAd hXd hbudget.1 hbudget.2 hseed

/-- Sufficient F3 specialization: sparse defects in a complete four-class host,
original integral divisibility and an original bounded almost packing imply a
physical triangle decomposition. All intermediates are constructed. -/
theorem four_class_decomposition (gamma C : ℝ) (hg : 0 < gamma)
    (hg1 : gamma ≤ 1) (hC : 1 ≤ C) :
    ∃ delta eps : ℝ, 0 < delta ∧ 0 < eps ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 4) (G0 : SimpleGraph V) [DecidableRel G0.Adj]
          (F : Finset (Sym2 V)) (phi : Finset V → ℝ),
          (∀ u v, G0.Adj u v ↔ p u ≠ p v) →
          (∀ i, gamma * Fintype.card V ≤ ((classSet p i).card : ℝ)) →
          F ⊆ G0.edgeFinset → DegBounded F (delta * Fintype.card V) →
          IsIntDiv p TypedApplicationLinks.F3
            (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset →
          IsRegularAlmostPacking p TypedApplicationLinks.F3
            (G0.deleteEdges (F : Set (Sym2 V))) C eps phi →
          HasDecomp p TypedApplicationLinks.F3
            (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset := by
  obtain ⟨rho,eps,hrho,heps,hconsumer⟩ := capacity_before_supply gamma C hg hg1 hC
  obtain ⟨delta,alpha,hd,ha,ha1,NX,hNX⟩ :=
    NeutralReserveProducerStage78.exists_neutral_reserve gamma rho hg hg1 hrho
  obtain ⟨NA,hNA⟩ := hconsumer alpha ha ha1
  refine ⟨min delta rho,eps,lt_min hd hrho,heps,max NX NA,?_⟩
  intro V _ _ hV p G0 _ F phi hG0 hsize hF hFd hdiv hseed
  classical
  have hFd' : DegBounded F (delta * Fintype.card V) := fun v =>
    (hFd v).trans (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Nat.cast_nonneg (Fintype.card V)))
  have hFdr : DegBounded F (rho * Fintype.card V) := fun v =>
    (hFd v).trans (mul_le_mul_of_nonneg_right (min_le_right _ _)
      (Nat.cast_nonneg (Fintype.card V)))
  obtain ⟨X,hX,hdX,hanti,hneutral⟩ :=
    hNX V (le_of_max_le_left hV) p G0 F hG0 hsize hFd'
  exact hNA V (le_of_max_le_right hV) p G0 F X phi hG0 hsize hF hFdr
    hdiv hX hdX hneutral hanti hseed

end PartitionedTriangleAbsorption.FourClassUnconditionalStage79
