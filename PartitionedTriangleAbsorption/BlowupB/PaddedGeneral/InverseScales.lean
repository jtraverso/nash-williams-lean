/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.HostRepairBound

@[expose] public section

/-! Explicit scales for an arbitrary nonnegative inverse constant. These replace
fixed numerical repair budgets; they do not supply the inverse or absorber. -/
namespace PaddedGeneral

noncomputable def inverseKappa (C ω : ℝ) : ℝ :=
  min (ω / 8) (ω ^ 12 / (216 * hostInverseConstant C))

noncomputable def inverseEpsilon (C ω : ℝ) : ℝ :=
  ω ^ 11 / (4 * hostInverseConstant C)

theorem inverse_scales_pos {C ω : ℝ} (hC : 0 ≤ C) (hω : 0 < ω) :
    0 < inverseKappa C ω ∧ 0 < inverseEpsilon C ω := by
  have hH : 0 < hostInverseConstant C := by unfold hostInverseConstant; positivity
  simp only [inverseKappa, inverseEpsilon]
  constructor <;> positivity

theorem inverse_epsilon_budget {C ω ε : ℝ} (hC : 0 ≤ C) (hω : 0 < ω)
    (hε : ε ≤ inverseEpsilon C ω) :
    (hostInverseConstant C / ω ^ 9) * ε ≤ ω ^ 2 / 4 := by
  have hH : 0 < hostInverseConstant C := by unfold hostInverseConstant; positivity
  calc
    _ ≤ (hostInverseConstant C / ω ^ 9) * inverseEpsilon C ω :=
      mul_le_mul_of_nonneg_left hε (by positivity)
    _ = _ := by unfold inverseEpsilon; field_simp

theorem inverse_kappa_budget {C ω κ : ℝ} (hC : 0 ≤ C) (hω : 0 < ω)
    (hκ : κ ≤ inverseKappa C ω) :
    κ ≤ ω / 8 ∧
    (hostInverseConstant C / ω ^ 9) * (2 * (27 / ω) * κ) ≤ ω ^ 2 / 4 := by
  have hH : 0 < hostInverseConstant C := by unfold hostInverseConstant; positivity
  refine ⟨hκ.trans (min_le_left _ _), ?_⟩
  have hk : κ ≤ ω ^ 12 / (216 * hostInverseConstant C) := hκ.trans (min_le_right _ _)
  calc
    _ ≤ (hostInverseConstant C / ω ^ 9) *
        (2 * (27 / ω) * (ω ^ 12 / (216 * hostInverseConstant C))) := by
      gcongr
    _ = _ := by field_simp; ring

theorem inverse_deletion_allocation {C ω ρ δ : ℝ}
    (hρ : ρ ≤ inverseKappa C ω / 8) (hδ : δ ≤ inverseKappa C ω / 8) :
    2 * δ + 2 * ρ ≤ inverseKappa C ω / 2 := by linarith

#print axioms inverse_scales_pos
#print axioms inverse_epsilon_budget
#print axioms inverse_kappa_budget
#print axioms inverse_deletion_allocation
end PaddedGeneral
