/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # A compatible scalar budget for the 36 / gamma^3 inverse

These inequalities do not construct the reserve or absorber. They are valid
for every order and can be used before choosing those geometric objects.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassBudgetStage75

noncomputable def deletionTolerance (gamma C : ℝ) : ℝ := gamma ^ 3 / (1024 * C ^ 2)
noncomputable def seedTolerance (gamma C : ℝ) : ℝ := gamma ^ 3 / (256 * C)

theorem tolerances_positive (gamma C : ℝ) (hg : 0 < gamma) (hC : 1 ≤ C) :
    0 < deletionTolerance gamma C ∧ 0 < seedTolerance gamma C := by
  have hc : 0 < C := by linarith
  constructor <;> dsimp [deletionTolerance, seedTolerance] <;> positivity

theorem compatible_budget (gamma C eps f a x : ℝ) (hg : 0 < gamma) (hC : 1 ≤ C)
    (heps : eps ≤ seedTolerance gamma C)
    (hf : f ≤ deletionTolerance gamma C)
    (ha : a ≤ deletionTolerance gamma C)
    (hx : x ≤ deletionTolerance gamma C) :
    72 * (f + a + x) ≤ gamma ^ 3 ∧
      72 * C * (eps + 2 * C * (a + x)) ≤ gamma ^ 3 := by
  have hc : 0 < C := by linarith
  have hg3 : 0 < gamma ^ 3 := by positivity
  have hc2 : 1 ≤ C ^ 2 := by nlinarith
  have htol : 216 * deletionTolerance gamma C ≤ gamma ^ 3 := by
    dsimp [deletionTolerance]
    rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  have hidentity : 72 * C * (seedTolerance gamma C +
      4 * C * deletionTolerance gamma C) = 9 / 16 * gamma ^ 3 := by
    dsimp [seedTolerance, deletionTolerance]
    field_simp
    ring
  constructor
  · calc
      72 * (f + a + x) ≤ 216 * deletionTolerance gamma C := by linarith
      _ ≤ gamma ^ 3 := htol
  · calc
      72 * C * (eps + 2 * C * (a + x)) ≤
          72 * C * (seedTolerance gamma C + 4 * C * deletionTolerance gamma C) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hax : a + x ≤ 2 * deletionTolerance gamma C := by linarith
        have hh := mul_le_mul_of_nonneg_left hax (show 0 ≤ 2 * C by positivity)
        linarith
      _ = 9 / 16 * gamma ^ 3 := hidentity
      _ ≤ gamma ^ 3 := by linarith

end PartitionedTriangleAbsorption.FourClassBudgetStage75
