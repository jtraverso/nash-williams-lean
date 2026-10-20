/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.HostSupply
import PartitionedTriangleAbsorption.ColouredHub.Families

/-! # The ordinary and typed anti-edge inputs for F1 and F2

Guarded two-root extensions give the ordinary common neighbours even for a
pair of endpoint classes which is itself forbidden. This uses only the finite
allowed-pair graphs of F1/F2 and imposes no completeness on the physical host.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.OnePart
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

theorem f1_allowed_common : ∀ a b : Fin 4, ∃ c,
    (∃ k, Link F1 a c k) ∧ (∃ k, Link F1 b c k) := by
  unfold Link F1
  decide

theorem f2_allowed_common : ∀ a b : Fin 4, ∃ c,
    (∃ k, Link F2 a c k) ∧ (∃ k, Link F2 b c k) := by
  unfold Link F2
  decide

theorem f1_allowed_of_triangle : ∀ i j k : Fin 4,
    ({i, j, k} : Multiset (Fin 4)) ∈ F1 →
      (∃ a, Link F1 i k a) ∧ (∃ a, Link F1 j k a) := by
  unfold Link F1
  decide

theorem f2_allowed_of_triangle : ∀ i j k : Fin 4,
    ({i, j, k} : Multiset (Fin 4)) ∈ F2 →
      (∃ a, Link F2 i k a) ∧ (∃ a, Link F2 j k a) := by
  unfold Link F2
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem guarded_F1_inputs (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (γ : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F1 i j k) 2 (γ * Fintype.card V)) :
    (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) ∧
    AntiEdgeful p F1 G γ ∧ AntiEdgeful part1 triFam G γ :=
  ⟨fun i => hs.class_card i,
    hs.to_antiEdgeful (by omega) F1 f1_allowed_of_triangle,
    hs.to_ordinaryAntiEdgeful (by omega) f1_allowed_common⟩

theorem guarded_F2_inputs (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (γ : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F2 i j k) 2 (γ * Fintype.card V)) :
    (∀ i, γ * Fintype.card V ≤ ((univ.filter fun v => p v = i).card : ℝ)) ∧
    AntiEdgeful p F2 G γ ∧ AntiEdgeful part1 triFam G γ :=
  ⟨fun i => hs.class_card i,
    hs.to_antiEdgeful (by omega) F2 f2_allowed_of_triangle,
    hs.to_ordinaryAntiEdgeful (by omega) f2_allowed_common⟩

#print axioms guarded_F1_inputs
#print axioms guarded_F2_inputs

end PaddedF12
