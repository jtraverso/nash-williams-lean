/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.Flex.Component

/-!
# Whole-family universal certificates at flexible scales

`UniversalCertFlex F`: the statement of `UniversalCert F` for every `(ω, δ, ρ)` with
`FlexScales ω δ ρ n`. The rigid certificate is the special case of the padded scales
(`universalCert_of_flex`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral

/-- Universal certificate at flexible scales. -/
def UniversalCertFlex (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω δ ρ : ℝ),
    FlexScales ω δ ρ (Fintype.card V) →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    UniversalAbsorbers p F G ρ δ

theorem universalCert_of_flex {F : Finset (Multiset (Fin 4))} (h : UniversalCertFlex F) :
    UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  exact h V p G ω (paddedAbsDelta ω) (paddedRho ω)
    (flexScales_padded ω _ hω hω1 (Nat.cast_nonneg _) hn) hG hs

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.universalCert_of_flex
