/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedThresholdCore

@[expose] public section

/-! # Scalar estimates for the reserve and the two effective nibbles -/

namespace PaddedF12.PaddedThresholds

open KeevashQuantitative PaddedInputs

noncomputable def reserveAlpha (ω : ℝ) : ℝ := paddedRho ω ^ 2 * ω / 12

noncomputable def finalEta (ω : ℝ) : ℝ := reserveAlpha ω ^ 2 / 256

theorem kappa_small {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    paddedKappa ω ≤ ω / 8 := by
  have hp : ω ^ 12 ≤ ω := pow_le_of_le_one hω.le hω1 (by decide)
  unfold paddedKappa
  norm_num
  linarith

theorem deletion_budget {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    2 * paddedAbsDelta ω + 2 * paddedRho ω ≤ paddedKappa ω / 2 := by
  have hr := paddedRho_le_absDelta hω.le hω1
  dsimp only [paddedAbsDelta] at hr ⊢
  linarith

theorem rho_le_one {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) : paddedRho ω ≤ 1 := by
  have hr := paddedRho_le_absDelta hω.le hω1
  have hk := kappa_small hω hω1
  dsimp only [paddedAbsDelta] at hr
  linarith

theorem alpha_pos {ω : ℝ} (hω : 0 < ω) : 0 < reserveAlpha ω := by
  unfold reserveAlpha
  have hr := paddedRho_pos hω
  positivity

theorem alpha_le_one {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) : reserveAlpha ω ≤ 1 := by
  have hr := paddedRho_pos hω
  have hr1 := rho_le_one hω hω1
  have hs : paddedRho ω ^ 2 ≤ 1 := pow_le_one₀ hr.le hr1
  have hm := mul_le_mul hs hω1 hω.le (by norm_num : (0 : ℝ) ≤ 1)
  unfold reserveAlpha
  nlinarith only [hm]

theorem alpha_eq (ω : ℝ) : reserveAlpha ω = ω ^ 53 / (12 * (2 : ℝ) ^ 524) := by
  unfold reserveAlpha paddedRho
  rw [div_pow, ← pow_mul, ← pow_mul]
  rw [show (53 : ℕ) = 52 + 1 from rfl, pow_succ]
  field_simp
  ac_rfl

theorem alpha_lower {ω : ℝ} (hω : 0 ≤ ω) : ω ^ 53 / (2 : ℝ) ^ 528 ≤ reserveAlpha ω := by
  rw [alpha_eq]
  apply div_le_div₀ (pow_nonneg hω _) le_rfl (by positivity)
  calc
    12 * (2 : ℝ) ^ 524 ≤ (2 : ℝ) ^ 4 * 2 ^ 524 :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = (2 : ℝ) ^ 528 := by rw [← pow_add]

theorem eta_pos {ω : ℝ} (hω : 0 < ω) : 0 < finalEta ω := by
  unfold finalEta
  have ha := alpha_pos hω
  positivity

theorem eta_le_one {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) : finalEta ω ≤ 1 := by
  have hs : reserveAlpha ω ^ 2 ≤ 1 := pow_le_one₀ (alpha_pos hω).le (alpha_le_one hω hω1)
  unfold finalEta
  linarith

theorem eta_lower {ω : ℝ} (hω : 0 ≤ ω) : ω ^ 106 / (2 : ℝ) ^ 1064 ≤ finalEta ω := by
  have hs := pow_le_pow_left₀ (div_nonneg (pow_nonneg hω _) (by positivity)) (alpha_lower hω) 2
  have heq : (ω ^ 53 / (2 : ℝ) ^ 528) ^ 2 / 256 = ω ^ 106 / (2 : ℝ) ^ 1064 := by
    rw [show (256 : ℝ) = (2 : ℝ) ^ 8 by norm_num]
    rw [div_pow, ← pow_mul, ← pow_mul, div_div, ← pow_add]
  rw [← heq]
  exact div_le_div_of_nonneg_right hs (by norm_num)

theorem initial_parameter {ω : ℝ} (hω : 0 < ω) (hω8 : ω ≤ 1 / 8) :
    min (ω / 8) (min 1 (ω ^ 2)) = ω ^ 2 := by
  have hω1 : ω ≤ 1 := by linarith
  have hs : ω ^ 2 ≤ 1 := pow_le_one₀ hω.le hω1
  rw [min_eq_right hs, min_eq_right (show ω ^ 2 ≤ ω / 8 by nlinarith)]

theorem final_parameter {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    min (reserveAlpha ω ^ 2 / 256) (min 1 (reserveAlpha ω ^ 2)) = finalEta ω := by
  apply min_eq_left
  apply le_min
  · exact eta_le_one hω hω1
  · have hsq := sq_nonneg (reserveAlpha ω)
    linarith

theorem padded_exponent_large (m : ℕ) : 128 ≤ hKT 4 m ^ 20 := by
  have hq := qT_four_ge m
  have hp : 1 ≤ qT 4 m ^ 3 := one_le_pow₀ (show 1 ≤ qT 4 m by omega)
  have hh : (2 : ℕ) ^ 50 ≤ hKT 4 m := Nat.pow_le_pow_right (by decide) (by omega)
  have hp20 : hKT 4 m ≤ hKT 4 m ^ 20 := by
    simpa only [pow_one] using pow_le_pow_right₀ (show 1 ≤ hKT 4 m from hKT_pos 4 m)
      (show 1 ≤ (20 : ℕ) by decide)
  have hsmall : 128 ≤ (2 : ℕ) ^ 50 := by norm_num
  exact hsmall.trans (hh.trans hp20)

theorem epsilon_polynomial (m : ℕ) {ω : ℝ} (hω : 0 < ω) (hω8 : ω ≤ 1 / 8) :
    ω ^ (hKT 4 m ^ 20) ≤ ω ^ 86 / (2 : ℝ) ^ 65 := by
  have hω1 : ω ≤ 1 := by linarith
  have h42 : ω ^ 42 ≤ 1 / (2 : ℝ) ^ 65 := by
    calc
      _ ≤ (1 / 8 : ℝ) ^ 42 := pow_le_pow_left₀ hω.le hω8 _
      _ ≤ _ := by norm_num
  calc
    _ ≤ ω ^ 128 := pow_le_pow_of_le_one hω.le hω1 (padded_exponent_large m)
    _ = ω ^ 86 * ω ^ 42 := by rw [← pow_add]
    _ ≤ ω ^ 86 * (1 / (2 : ℝ) ^ 65) := mul_le_mul_of_nonneg_left h42 (by positivity)
    _ = _ := by ring

theorem initial_load_tolerance (m : ℕ) {ω : ℝ} (hω : 0 < ω) (hω8 : ω ≤ 1 / 8) :
    ω ^ (hKT 4 m ^ 20) ≤ loadTolerance (min (ω / 8) (min 1 (ω ^ 2))) := by
  rw [initial_parameter hω hω8]
  have hs : ω ^ 2 ≤ 1 := pow_le_one₀ hω.le (by linarith)
  have hl := loadTolerance_polynomial (ω ^ 2) (by positivity) hs
  rw [← pow_mul] at hl
  exact (epsilon_polynomial m hω hω8).trans hl

theorem epsilon_repair_budget (m : ℕ) {ω : ℝ} (hω : 0 < ω) (hω8 : ω ≤ 1 / 8) :
    ((2 : ℝ) ^ 32 / ω ^ 9) * ω ^ (hKT 4 m ^ 20) ≤ ω ^ 2 / 4 := by
  have hε := mul_le_mul_of_nonneg_left (epsilon_polynomial m hω hω8)
    (show 0 ≤ (2 : ℝ) ^ 32 / ω ^ 9 by positivity)
  have heq : ((2 : ℝ) ^ 32 / ω ^ 9) * (ω ^ 86 / (2 : ℝ) ^ 65) =
      ω ^ 77 / (2 : ℝ) ^ 33 := by
    rw [show (86 : ℕ) = 9 + 77 from rfl, pow_add,
      show (65 : ℕ) = 32 + 33 from rfl, pow_add]
    field_simp
  rw [heq] at hε
  apply hε.trans
  apply div_le_div₀ (sq_nonneg ω)
  · exact pow_le_pow_of_le_one hω.le (by linarith) (by decide)
  · norm_num
  · norm_num

#print axioms alpha_lower
#print axioms eta_lower
#print axioms initial_load_tolerance
#print axioms epsilon_repair_budget

end PaddedF12.PaddedThresholds
