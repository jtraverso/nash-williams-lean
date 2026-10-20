/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.StructuralIntegrationStage71
public import PartitionedTriangleAbsorption.PackingRestriction
public import PartitionedTriangleAbsorption.TypedLoadNecessity

/-! # Preparing the fractional seed on the same constructed absorber complement

The reserve is retained. This constructs an almost seed and proves that its
defect has zero annihilating charges. It does not assert a positive exact repair.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FractionalPreparationStage71

open Finset TypedLoadNecessity TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem seed_and_neutral_defect (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset (Sym2 V))
    (hAG : A ⊆ G.edgeFinset) (hdiv : IsIntDiv p F G.edgeFinset)
    (hA : HasDecomp p F A) (C eps delta : ℝ) (hC : 0 < C)
    (hn : 0 < Fintype.card V) (hAd : DegBounded A (2 * delta * Fintype.card V))
    (phi : Finset V → ℝ) (hseed : IsRegularAlmostPacking p F G C eps phi) :
    let H := G.deleteEdges (A : Set (Sym2 V))
    IsIntDiv p F H.edgeFinset ∧ IsRegularAlmostPacking p F H C (eps + 4 * C * delta) phi ∧
      ∀ l : Fin t → Fin t → ℤ, Annihilates F l →
        ∑ e ∈ H.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
          (1 - edgeLoad p F H phi e) = 0 := by
  classical
  dsimp only
  let H := G.deleteEdges (A : Set (Sym2 V))
  have hHdiv : IsIntDiv p F H.edgeFinset := by
    rw [SimpleGraph.edgeFinset_deleteEdges]
    exact isIntDiv_sdiff_of_hasDecomp hdiv hA hAG
  have hs := PackingRestriction.regularAlmostPacking_deleteEdges A hC hn hAd hseed
  have hnR : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have heq : eps + 2 * C * (2 * delta * Fintype.card V) / Fintype.card V =
      eps + 4 * C * delta := by field_simp; ring
  rw [heq] at hs
  refine ⟨hHdiv, hs, ?_⟩
  intro l hl
  have hbalance := annihilator_of_isIntDiv hHdiv hl
  have hload := annihilator_load_identity p F H phi hl
  rw [pairFun_edgeVec] at hbalance
  change (∑ e ∈ H.edgeFinset, (pairFun l (pairVec p e) : ℝ) *
    (1 - edgeLoad p F H phi e)) = 0
  simp only [mul_sub, mul_one, sum_sub_distrib]
  rw [hload, sub_zero]
  exact_mod_cast hbalance

/-- The actual producer, its almost seed, and its neutral defect share one A.
The coefficients and threshold precede G, X, phi and every leftover. -/
theorem constructed_absorber_with_seed (γ ζ : ℝ) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hζ : 0 < ζ) :
    ∃ δ lam rho : ℝ, 0 < δ ∧ 0 < lam ∧ 0 < rho ∧ δ ≤ ζ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (cls : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
        (∀ a b, G.Adj a b ↔ cls a ≠ cls b) →
        (∀ i, γ * Fintype.card V ≤
          ((ClassRepresentativesStage65.classSet cls i).card : ℝ)) →
        IsIntDiv cls F3 G.edgeFinset →
        ∀ (X : Finset (Sym2 V)), X ⊆ G.edgeFinset →
          DegBounded X (2 * rho * Fintype.card V) →
        ∀ (C eps : ℝ), 0 < C → ∀ phi : Finset V → ℝ,
          IsRegularAlmostPacking cls F3 G C eps phi →
          ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
            HasDecomp cls F3 A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
            (∀ L ⊆ X, IsIntDiv cls F3 L → HasDecomp cls F3 (A ∪ L)) ∧
            IsIntDiv cls F3 (G.deleteEdges (A : Set (Sym2 V))).edgeFinset ∧
            IsRegularAlmostPacking cls F3 (G.deleteEdges (A : Set (Sym2 V)))
              C (eps + 4 * C * δ) phi ∧
            ∀ l : Fin 4 → Fin 4 → ℤ, Annihilates F3 l →
              ∑ e ∈ (G.deleteEdges (A : Set (Sym2 V))).edgeFinset,
                (pairFun l (pairVec cls e) : ℝ) *
                  (1 - edgeLoad cls F3 (G.deleteEdges (A : Set (Sym2 V))) phi e) = 0 := by
  obtain ⟨δ, lam, rho, hδ, hlam, hrho, hδζ, N, hN⟩ :=
    StructuralIntegrationStage71.exists_fixed_scales_below γ ζ hγ hγ1 hζ
  refine ⟨δ, lam, rho, hδ, hlam, hrho, hδζ, max N 1, ?_⟩
  intro V _ _ hn cls G _ hG hsize hdiv X hXG hX C eps hC phi hseed
  obtain ⟨A, hAG, hAX, hA, hAd, habs⟩ :=
    hN V (le_of_max_le_left hn) cls G hG hsize X hXG hX
  obtain ⟨hHdiv, hHseed, hneutral⟩ := seed_and_neutral_defect cls F3 G A hAG
    hdiv hA C eps δ hC (by have := le_of_max_le_right hn; omega) hAd phi hseed
  exact ⟨A, hAG, hAX, hA, hAd, habs, hHdiv, hHseed, hneutral⟩

end PartitionedTriangleAbsorption.FractionalPreparationStage71
