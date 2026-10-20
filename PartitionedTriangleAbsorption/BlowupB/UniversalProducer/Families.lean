/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Target

/-!
# The producer target, unconditionally, for the families with a proved refiner

For `F1`, `F2`, `F3` the refiner and private terminal are already constructed
(`universal_F12_uniform`, `universal_F3_uniform`).  Here only the parameter
handshake is added: `δ` is restricted to `(0, ω/(64(S+1))]` and then freed by
monotonicity, `ρ = refinerRho C ω (min δ δ₀)`, `N = ⌈1/ρ⌉`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General

theorem F3_allowed_eq : (fun i j : Fin 4 => ∃ k, Link F3 i j k) = (fun i j => i ≠ j) := by
  funext i j
  exact propext (F3_allowed_iff i j)

/-- **F3: the producer target holds unconditionally** (with an order `S ≥ 4`). -/
theorem producerTarget_F3 : ∃ S : ℕ, 4 ≤ S ∧ ProducerTarget F3 S := by
  obtain ⟨S, C, _, _, hmain⟩ := universal_F3_uniform
  refine ⟨max S 4, le_max_right _ _, producerTarget_mono_order ?_ (le_max_left S 4)⟩
  refine producerTarget_of_uniform F3 S C ?_
  intro V _ _ p G _ γ δ hG hs hγ hγ1 hδ hsmall hn
  have hG' : ∀ x y, G.Adj x y → p x ≠ p y := fun x y h =>
    (F3_allowed_iff _ _).mp (hG x y h)
  rw [F3_allowed_eq] at hs
  exact hmain p G γ δ hG' hs hγ hγ1 hδ hsmall hn

/-- **F1: the producer target holds unconditionally**, order `2^21`. -/
theorem producerTarget_F1 : ProducerTarget F1 (2 ^ 21) := by
  obtain ⟨S, C, hS, _, _, _, hmain⟩ := PaddedF12.universal_F1_uniform
  subst hS
  exact producerTarget_of_uniform F1 _ C fun V _ _ p G _ γ δ => hmain p G γ δ

/-- **F2: the producer target holds unconditionally**, order `2^21`. -/
theorem producerTarget_F2 : ProducerTarget F2 (2 ^ 21) := by
  obtain ⟨S, C, hS, _, _, _, hmain⟩ := PaddedF12.universal_F2_uniform
  subst hS
  exact producerTarget_of_uniform F2 _ C fun V _ _ p G _ γ δ => hmain p G γ δ

/-- The three application families satisfy `FamilyFacts` and the target. -/
theorem producerTarget_F123 :
    (PaddedGeneral.FamilyFacts F1 ∧ ProducerTarget F1 (2 ^ 21)) ∧
    (PaddedGeneral.FamilyFacts F2 ∧ ProducerTarget F2 (2 ^ 21)) ∧
    (PaddedGeneral.FamilyFacts F3 ∧ ∃ S, 4 ≤ S ∧ ProducerTarget F3 S) :=
  ⟨⟨PaddedGeneral.familyFacts_F1, producerTarget_F1⟩,
    ⟨PaddedGeneral.familyFacts_F2, producerTarget_F2⟩,
    ⟨PaddedGeneral.familyFacts_F3, producerTarget_F3⟩⟩

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
