/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedThresholdScales

@[expose] public section

/-! # Every final order requirement is covered by the one uniform threshold -/

namespace PaddedF12.PaddedThresholds

open KeevashQuantitative PaddedInputs
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer

theorem initial_polynomial {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    packingPolynomial (27 / ω) (ω ^ 2) ≤ (2 : ℝ) ^ 6700 / ω ^ 8040 := by
  have hb : 27 / ω + 1 ≤ (2 : ℝ) ^ 5 / ω := by
    apply (le_div_iff₀ hω).mpr
    rw [add_mul, div_mul_cancel₀ _ hω.ne', one_mul]
    norm_num
    linarith
  calc
    _ ≤ (2 : ℝ) ^ 6500 * ((2 : ℝ) ^ 5 / ω) ^ 40 / (ω ^ 2) ^ 4000 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 40) (by positivity)
    _ = _ := by
      simpa only [pow_zero, div_one] using monomial_normalization ω hω 6500 5 40 2 0 4000

theorem final_polynomial {ω : ℝ} (hω : 0 < ω) (hω1 : ω ≤ 1) :
    packingPolynomial (54 / ω) (finalEta ω) ≤ (2 : ℝ) ^ 4262740 / ω ^ 424040 := by
  have hb : 54 / ω + 1 ≤ (2 : ℝ) ^ 6 / ω := by
    apply (le_div_iff₀ hω).mpr
    rw [add_mul, div_mul_cancel₀ _ hω.ne', one_mul]
    norm_num
    linarith
  calc
    _ ≤ (2 : ℝ) ^ 6500 * ((2 : ℝ) ^ 6 / ω) ^ 40 /
        (ω ^ 106 / (2 : ℝ) ^ 1064) ^ 4000 := by
      apply div_le_div₀ (by positivity)
      · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb 40) (by positivity)
      · positivity
      · exact pow_le_pow_left₀ (by positivity) (eta_lower hω.le) 4000
    _ = _ := monomial_normalization ω hω 6500 6 40 106 1064 4000

theorem cover_rounding_polynomial {ω : ℝ} (hω : 0 < ω) :
    256 / reserveAlpha ω ^ 2 ≤ (2 : ℝ) ^ 1064 / ω ^ 106 := by
  have ha := alpha_pos hω
  calc
    _ = 1 / finalEta ω := by unfold finalEta; field_simp
    _ ≤ 1 / (ω ^ 106 / (2 : ℝ) ^ 1064) :=
      div_le_div₀ (by norm_num) le_rfl (by positivity) (eta_lower hω.le)
    _ = _ := by field_simp

theorem rho_order (m n : ℕ) (hn : orderThreshold < n) (ω : ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hdensity : (n : ℝ) ^ (-δKT 4 m) < ω) :
    1 ≤ paddedRho ω * n := by
  have hm := monomial_order m n hn ω hω hω1 hdensity 262 26
    (by norm_num) (by norm_num [exponentD])
  have hi : 1 / paddedRho ω ≤ (n : ℝ) := by
    simpa only [paddedRho, one_div, inv_div] using hm.le
  have hh := (div_le_iff₀ (paddedRho_pos hω)).mp hi
  simpa only [mul_comm] using hh

theorem four_order (m n : ℕ) (hn : orderThreshold < n) (ω : ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hdensity : (n : ℝ) ^ (-δKT 4 m) < ω) :
    4 ≤ ω * n := by
  have hm := monomial_order m n hn ω hω hω1 hdensity 2 1
    (by norm_num) (by norm_num [exponentD])
  have hi : 4 / ω ≤ (n : ℝ) := by
    norm_num at hm
    exact hm.le
  have hh := (div_le_iff₀ hω).mp hi
  simpa only [mul_comm] using hh

theorem reserve_order (m n : ℕ) (hn : orderThreshold < n) (ω : ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hdensity : (n : ℝ) ^ (-δKT 4 m) < ω) :
    (2 : ℝ) ^ 27 * (paddedRho ω)⁻¹ ^ 9 * ω⁻¹ ^ 6 ≤ n := by
  have hm := monomial_order m n hn ω hω hω1 hdensity 2385 240
    (by norm_num) (by norm_num [exponentD])
  have heq : (2 : ℝ) ^ 27 * (paddedRho ω)⁻¹ ^ 9 * ω⁻¹ ^ 6 =
      (2 : ℝ) ^ 2385 / ω ^ 240 :=
    reciprocal_normalization ω hω 27 26 262 9 6
  rw [heq]
  exact hm.le

theorem initial_threshold_order (m n : ℕ) (hn : orderThreshold < n) (ω : ℝ)
    (hω : 0 < ω) (hω8 : ω ≤ 1 / 8) (hdensity : (n : ℝ) ^ (-δKT 4 m) < ω) :
    packingThreshold (27 / ω) (min (ω / 8) (min 1 (ω ^ 2))) ≤ n := by
  have hω1 : ω ≤ 1 := by linarith
  rw [initial_parameter hω hω8]
  have hp := packingThreshold_cast_le (27 / ω) (ω ^ 2) (by positivity) (by positivity)
    (pow_le_one₀ hω.le hω1)
  have hm := monomial_order m n hn ω hω hω1 hdensity 6700 8040
    (by norm_num) (by norm_num [exponentD])
  have hreal := (hp.trans (initial_polynomial hω hω1)).trans_lt hm
  exact_mod_cast hreal.le

theorem final_threshold_order (m n : ℕ) (hn : orderThreshold < n) (ω : ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hdensity : (n : ℝ) ^ (-δKT 4 m) < ω) :
    coverDownThreshold (54 / ω) (reserveAlpha ω) ≤ n := by
  unfold coverDownThreshold
  rw [final_parameter hω hω1]
  apply max_le
  · have hp := packingThreshold_cast_le (54 / ω) (finalEta ω) (by positivity)
      (eta_pos hω) (eta_le_one hω hω1)
    have hm := monomial_order m n hn ω hω hω1 hdensity 4262740 424040
      (by norm_num) (by norm_num [exponentD])
    have hreal := (hp.trans (final_polynomial hω hω1)).trans_lt hm
    exact_mod_cast hreal.le
  · apply Nat.ceil_le.mpr
    have hm := monomial_order m n hn ω hω hω1 hdensity 1064 106
      (by norm_num) (by norm_num [exponentD])
    exact ((cover_rounding_polynomial hω).trans_lt hm).le

/-- All numerical premises consumed by the geometric proof. -/
structure NumericInputs (m n : ℕ) (ω : ℝ) : Prop where
  omega_pos : 0 < ω
  omega_le_one : ω ≤ 1
  rho_le_one : paddedRho ω ≤ 1
  alpha_pos : 0 < reserveAlpha ω
  alpha_le_one : reserveAlpha ω ≤ 1
  rho_n : 1 ≤ paddedRho ω * n
  class_n : 4 ≤ ω * n
  reserve_n : (2 : ℝ) ^ 27 * (paddedRho ω)⁻¹ ^ 9 * ω⁻¹ ^ 6 ≤ n
  initial_n : packingThreshold (27 / ω) (min (ω / 8) (min 1 (ω ^ 2))) ≤ n
  final_n : coverDownThreshold (54 / ω) (reserveAlpha ω) ≤ n
  initial_tolerance : ω ^ (hKT 4 m ^ 20) ≤ loadTolerance (min (ω / 8) (min 1 (ω ^ 2)))
  initial_repair : ((2 : ℝ) ^ 32 / ω ^ 9) * ω ^ (hKT 4 m ^ 20) ≤ ω ^ 2 / 4
  deletion_repair : ((2 : ℝ) ^ 32 / ω ^ 9) * (2 * (27 / ω) * paddedKappa ω) ≤ ω ^ 2 / 4
  kappa_cap : paddedKappa ω ≤ ω / 8
  deletion_cap : 2 * paddedAbsDelta ω + 2 * paddedRho ω ≤ paddedKappa ω / 2

theorem numeric_inputs (m n : ℕ) (hn : orderThreshold < n) (ω : ℝ)
    (hdensity : (n : ℝ) ^ (-δKT 4 m) < ω) (hω8 : ω < 1 / 8) :
    NumericInputs m n ω := by
  have hn0 : (0 : ℝ) < n := by
    have hnN : 0 < n := by
      unfold orderThreshold uniformThreshold at hn
      omega
    exact_mod_cast hnN
  have hω : 0 < ω := (Real.rpow_pos_of_pos hn0 _).trans hdensity
  have hω1 : ω ≤ 1 := by linarith
  exact ⟨hω, hω1, rho_le_one hω hω1, alpha_pos hω, alpha_le_one hω hω1,
    rho_order m n hn ω hω hω1 hdensity,
    four_order m n hn ω hω hω1 hdensity,
    reserve_order m n hn ω hω hω1 hdensity,
    initial_threshold_order m n hn ω hω hω8.le hdensity,
    final_threshold_order m n hn ω hω hω1 hdensity,
    initial_load_tolerance m hω hω8.le, epsilon_repair_budget m hω hω8.le,
    padded_repair_budget hω, kappa_small hω hω1, deletion_budget hω hω1⟩

/-- Both constants are chosen before the padding, the order and the density. -/
theorem uniform_numeric_inputs :
    ∃ ω0 : ℝ, ω0 = 1 / 8 ∧ 0 < ω0 ∧ ∃ n0 : ℕ, n0 = orderThreshold ∧
      ∀ m n : ℕ, n0 < n → ∀ ω : ℝ,
        (n : ℝ) ^ (-δKT 4 m) < ω → ω < ω0 → NumericInputs m n ω := by
  exact ⟨1 / 8, rfl, by norm_num, orderThreshold, rfl, numeric_inputs⟩

#print axioms initial_polynomial
#print axioms final_polynomial
#print axioms reserve_order
#print axioms initial_threshold_order
#print axioms final_threshold_order
#print axioms uniform_numeric_inputs

end PaddedF12.PaddedThresholds
