/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.StructuralIntegrationStage71

/-! # Shield original defects by treating them as forbidden reserve edges

The complete-host producer already avoids its entire supplied reserve. Feeding
it F union X makes its absorber lie in G0 - F and still absorb every divisible
subset of X. No divisibility of F or of the enlarged reserve is required.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassPerturbedAbsorberStage75

open Finset TypedApplicationLinks

theorem absorber_avoiding_original_defects (gamma zeta : ℝ)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hz : 0 < zeta) :
    ∃ delta lam rho : ℝ, 0 < delta ∧ 0 < lam ∧ 0 < rho ∧ delta ≤ zeta ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 4) (G0 : SimpleGraph V) [DecidableRel G0.Adj]
          (F X : Finset (Sym2 V)),
          (∀ u v, G0.Adj u v ↔ p u ≠ p v) →
          (∀ i, gamma * Fintype.card V ≤
            ((ClassRepresentativesStage65.classSet p i).card : ℝ)) →
          F ⊆ G0.edgeFinset → X ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset →
          DegBounded (F ∪ X) (2 * rho * Fintype.card V) →
          ∃ A : Finset (Sym2 V),
            A ⊆ (G0.deleteEdges (F : Set (Sym2 V))).edgeFinset ∧ Disjoint A X ∧
            HasDecomp p F3 A ∧ DegBounded A (2 * delta * Fintype.card V) ∧
            ∀ L ⊆ X, IsIntDiv p F3 L → HasDecomp p F3 (A ∪ L) := by
  obtain ⟨delta,lam,rho,hd,hl,hr,hdz,N,hN⟩ :=
    StructuralIntegrationStage71.exists_fixed_scales_below gamma zeta hg hg1 hz
  refine ⟨delta,lam,rho,hd,hl,hr,hdz,N,?_⟩
  intro V _ _ hV p G0 _ F X hG0 hsize hF hX hdFX
  classical
  have hY : F ∪ X ⊆ G0.edgeFinset := union_subset hF
    (hX.trans (SimpleGraph.edgeFinset_mono (SimpleGraph.deleteEdges_le _)))
  obtain ⟨A,hAG,hAY,hA,hAd,habs⟩ := hN V hV p G0 hG0 hsize (F ∪ X) hY hdFX
  refine ⟨A, ?_, hAY.mono_right subset_union_right, hA, hAd, ?_⟩
  · rw [SimpleGraph.edgeFinset_deleteEdges]
    intro e he
    refine mem_sdiff.mpr ⟨hAG he, ?_⟩
    intro heF
    exact disjoint_left.mp hAY he (mem_union_left X heF)
  · intro L hLX hdiv
    exact habs L (hLX.trans subset_union_right) hdiv

end PartitionedTriangleAbsorption.FourClassPerturbedAbsorberStage75
