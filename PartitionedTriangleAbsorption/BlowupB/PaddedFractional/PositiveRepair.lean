/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.InverseEstimates

/-! # Converting a small signed correction into an exact positive packing -/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem exactWeights_of_bounded_correction (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : 0 < Fintype.card V)
    (φ w : TriangleChain V)
    (hφ : ∀ T, IsCopy p F G T → ω ^ 2 / Fintype.card V ≤ φ T ∧
      φ T ≤ (27 / ω) / Fintype.card V)
    (hws : CopySupported p F G w)
    (hwb : ∀ T, IsCopy p F G T → |w T| ≤ (ω ^ 2 / 2) / Fintype.card V)
    (hwe : ∀ e ∈ G.edgeFinset, boundary w e =
      1 - ∑ T ∈ copies p F G with e ∈ triEdges T, φ T) :
    ∃ ψ : TriangleChain V,
      (∀ T, IsCopy p F G T → 0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
      ∀ e ∈ G.edgeFinset, (∑ T ∈ copies p F G with e ∈ triEdges T, ψ T) = 1 := by
  classical
  refine ⟨fun T => φ T + w T, ?_, ?_⟩
  · intro T hT
    exact positive_repair_weights ω (Fintype.card V) (φ T) (w T) hω hω1
      (by exact_mod_cast hn) (hφ T hT).1 (hφ T hT).2 (hwb T hT)
  · intro e he
    rw [sum_add_distrib, ← boundary_eq_copy_load p F G w hws e, hwe e he]
    ring

theorem correction_budget (K ε b κ ω n : ℝ) (hn : 0 ≤ n)
    (hε : K * ε ≤ ω ^ 2 / 4) (hκ : K * (2 * b * κ) ≤ ω ^ 2 / 4) :
    K * (ε + 2 * b * κ) / n ≤ (ω ^ 2 / 2) / n := by
  apply div_le_div_of_nonneg_right _ hn
  rw [mul_add]
  linarith

#print axioms exactWeights_of_bounded_correction
#print axioms correction_budget

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
