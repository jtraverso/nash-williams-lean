/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Lattice

/-! # The application families F0–F3

All four families consist of size-three types and satisfy `ThreeStepLinks`
(`TypedTransformerLabels`), so both producers apply to them verbatim.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open TypedApplicationLinks TypedTransformer

theorem F0_card_three : ∀ τ ∈ F0, Multiset.card τ = 3 := by decide

theorem F1_card_three : ∀ τ ∈ F1, Multiset.card τ = 3 := by decide

theorem F2_card_three : ∀ τ ∈ F2, Multiset.card τ = 3 := by decide

theorem F3_card_three : ∀ τ ∈ F3, Multiset.card τ = 3 := by decide

end PartitionedTriangleAbsorption.ColouredHub
