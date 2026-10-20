/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.ThreeStepFamily
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Families
import PartitionedTriangleAbsorption.BlowupB.Theorem147Bridge

/-! Paper II entry points: the absorber premise is discharged by a proved
producer. The F1/F2 corollary uses the local idealized-host definition; import
identification with the separate Nash-Williams project is not asserted here.
F0 and families outside the stated hypotheses are not claimed. -/

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.BlowupB
open PartitionedTriangleAbsorption.BlowupB.UniversalProducer


theorem keevashTypedSpec_F123 {F : Finset (Multiset (Fin 4))}
    (hF : F = F1 ∨ F = F2 ∨ F = F3) : KeevashTypedSpec F := by
  rcases hF with rfl | rfl | rfl
  · exact keevashTypedSpec_of_threeStepLinks F1 familyFacts_F1 F1_three_step
  · exact keevashTypedSpec_of_threeStepLinks F2 familyFacts_F2 F2_three_step
  · exact keevashTypedSpec_of_threeStepLinks F3 familyFacts_F3 F3_three_step

/-- Nearly complete balanced blowups for all three application families. -/
theorem nearlyComplete_F123 {F : Finset (Multiset (Fin 4))}
    (hF : F = F1 ∨ F = F2 ∨ F = F3) :
    ∃ η : ℝ, 0 < η ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, (1 / 4 - η) * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ) ∧
          ((univ.filter fun v => p v = i).card : ℝ) ≤ (1 / 4 + η) * Fintype.card V) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset :=
  teoremaB_F123 hF (keevashTypedSpec_F123 hF)

/-- The local F1/F2 idealized-host application, with no certificate premise. -/
theorem idealized_F12 {F : Finset (Multiset (Fin 4))}
    (hF : F = F1 ∨ F = F2) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
        (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
        IsIntDiv p F G.edgeFinset → IsIdealizedNW F ε G p →
        HasDecomp p F G.edgeFinset :=
  theorem147_of_keevash hF (keevashTypedSpec_F123 (hF.imp_right Or.inl))

#print axioms keevashTypedSpec_of_threeStepLinks
#print axioms keevashTypedSpec_F123
#print axioms nearlyComplete_F123
#print axioms idealized_F12

end PaddedGeneral.RealInverse
