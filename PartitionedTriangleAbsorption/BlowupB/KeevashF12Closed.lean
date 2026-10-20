/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.Theorem147Bridge
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.VerifiedF12

/-! # BlowupB.KeevashF12Closed — the padded Keevash interface for F₁ and F₂, closed

The independent package `PaddedF12` (delivery `KeevashPadded_F1_F2_20261012.zip`) proves
`PaddedInputs.KeevashPaddedSpec F` for `F ∈ {F₁, F₂}`, a literal transcription of
`BlowupB.KeevashPadded.KeevashPaddedSpec` in a separate namespace. The two propositions are
definitionally equal (`change` below is checked by the kernel).

Consequences, with no remaining hypothesis:
* `keevashTypedSpec_F1`, `keevashTypedSpec_F2` (via `keevashTypedSpec_of_padded`);
* `teoremaB_F1`, `teoremaB_F2`: Theorem B for ε-balanced, nearly complete, integrally divisible
  `F₁`/`F₂`-blowups (via `teoremaB_F123`);
* `theorem147_F1`, `theorem147_F2`: the statement of `Theorem147F1Statement` /
  `Theorem147F2Statement` of NW 1.8 (with `IsIdealizedT` copied as `IsIdealizedNW`).

This file is not a `module` because `PaddedF12.VerifiedF12` is not one.
-/

namespace PartitionedTriangleAbsorption.BlowupB

open Finset TypedApplicationLinks

theorem keevashPaddedSpec_F1 : KeevashPaddedSpec F1 := by
  change PaddedInputs.KeevashPaddedSpec F1
  exact PaddedF12.keevashPaddedSpec_F1

theorem keevashPaddedSpec_F2 : KeevashPaddedSpec F2 := by
  change PaddedInputs.KeevashPaddedSpec F2
  exact PaddedF12.keevashPaddedSpec_F2

theorem keevashTypedSpec_F1 : KeevashTypedSpec F1 :=
  keevashTypedSpec_of_padded (by unfold F1; decide) keevashPaddedSpec_F1

theorem keevashTypedSpec_F2 : KeevashTypedSpec F2 :=
  keevashTypedSpec_of_padded (by unfold F2; decide) keevashPaddedSpec_F2

/-- **Theorem B for `F₁` and `F₂`** (ε-balanced, nearly complete), unconditional. -/
theorem teoremaB_F12 {F : Finset (Multiset (Fin 4))} (hF : F = F1 ∨ F = F2) :
    ∃ η : ℝ, 0 < η ∧ ∃ (N : ℕ) (δ : ℝ), 0 < δ ∧
      ∀ {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4) (d : ℕ), N ≤ Fintype.card V →
        (∀ u v, G.Adj u v → AllowedPair F (p u) (p v)) → (∀ v, missDeg p F G v ≤ d) →
        (d : ℝ) ≤ δ * Fintype.card V →
        (∀ i, (1 / 4 - η) * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ) ∧
          ((univ.filter fun v => p v = i).card : ℝ) ≤ (1 / 4 + η) * Fintype.card V) →
        IsIntDiv p F G.edgeFinset → HasDecomp p F G.edgeFinset := by
  rcases hF with rfl | rfl
  · exact teoremaB_F123 (Or.inl rfl) keevashTypedSpec_F1
  · exact teoremaB_F123 (Or.inr (Or.inl rfl)) keevashTypedSpec_F2

/-- **NW 1.8, entry F₁** (`Theorem147F1Statement`, `IsIdealizedT` unfolded), unconditional. -/
theorem theorem147_F1 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      IsIntDiv p F1 G.edgeFinset → IsIdealizedNW F1 ε G p → HasDecomp p F1 G.edgeFinset :=
  theorem147_of_padded (Or.inl rfl) keevashPaddedSpec_F1

/-- **NW 1.8, entry F₂** (`Theorem147F2Statement`, `IsIdealizedT` unfolded), unconditional. -/
theorem theorem147_F2 :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
      IsIntDiv p F2 G.edgeFinset → IsIdealizedNW F2 ε G p → HasDecomp p F2 G.edgeFinset :=
  theorem147_of_padded (Or.inr rfl) keevashPaddedSpec_F2

end PartitionedTriangleAbsorption.BlowupB

#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_F1
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashPaddedSpec_F2
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashTypedSpec_F1
#print axioms PartitionedTriangleAbsorption.BlowupB.keevashTypedSpec_F2
#print axioms PartitionedTriangleAbsorption.BlowupB.teoremaB_F12
#print axioms PartitionedTriangleAbsorption.BlowupB.theorem147_F1
#print axioms PartitionedTriangleAbsorption.BlowupB.theorem147_F2
