/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedScales

/-! # Every padding parameter supplies the fixed query order used above -/

namespace PaddedInputs

theorem qT_four_ge (m : ℕ) : 12 ≤ qT 4 m := by
  unfold qT
  omega

theorem hKT_pos (t m : ℕ) : 0 < hKT t m := by
  unfold hKT
  positivity

theorem padded_query_bounds (m : ℕ) :
    3 ≤ qT 4 m ∧ qT 4 m ≤ qT 4 m * hKT 4 m ∧
      (2 ^ 21 : ℕ) + 1 ≤ qT 4 m * hKT 4 m := by
  have hq := qT_four_ge m
  have hpow : 1 ≤ (qT 4 m) ^ 3 := one_le_pow₀ (show 1 ≤ qT 4 m by omega)
  have he : 22 ≤ 50 * (qT 4 m) ^ 3 := by omega
  have hH : (2 : ℕ) ^ 22 ≤ hKT 4 m := Nat.pow_le_pow_right (by decide) he
  have hHpos := hKT_pos 4 m
  refine ⟨by omega, ?_, ?_⟩
  · nlinarith only [hq, hHpos]
  · norm_num at hH ⊢
    nlinarith only [hq, hH]

#print axioms padded_query_bounds

end PaddedInputs
