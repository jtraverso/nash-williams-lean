/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootQueryBudgetStage59

/-! # Explicit size thresholds for four-label degree queries -/

@[expose] public section

namespace PartitionedTriangleAbsorption.DegreeReserveBudgetStage115

theorem failure_budget (n β ρ : ℝ) (hn : 0 ≤ n) (hβ : 0 ≤ β)
    (hsize : 64 ≤ β ^ 2 * ρ ^ 4 * n) (hdegrees : 2 ≤ ρ ^ 4 * n) :
    n * Real.exp (-2 * ρ ^ 2 * n) +
      (n * 4) * Real.exp (-ρ ^ 2 * β * n / 2) ≤ 3 / 4 := by
  have hpow1 := Real.pow_div_factorial_le_exp (2 * ρ ^ 2 * n)
    (by positivity) 2
  have hpow2 := Real.pow_div_factorial_le_exp (ρ ^ 2 * β * n / 2)
    (by positivity) 2
  norm_num [mul_pow] at hpow1 hpow2
  have hd := mul_le_mul_of_nonneg_right hdegrees (show 0 ≤ 2 * n by positivity)
  have hs := mul_le_mul_of_nonneg_right hsize hn
  have he1 : 4 * n ≤ Real.exp (2 * ρ ^ 2 * n) := by nlinarith
  have he2 : 8 * n ≤ Real.exp (ρ ^ 2 * β * n / 2) := by nlinarith
  have ht1 : n / Real.exp (2 * ρ ^ 2 * n) ≤ 1 / 4 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have ht2 : (n * 4) / Real.exp (ρ ^ 2 * β * n / 2) ≤ 1 / 2 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have hneg1 : -2 * ρ ^ 2 * n = -(2 * ρ ^ 2 * n) := by ring
  have hneg2 : -ρ ^ 2 * β * n / 2 = -(ρ ^ 2 * β * n / 2) := by ring
  rw [hneg1, hneg2]
  simp only [Real.exp_neg, ← div_eq_mul_inv]
  linarith

theorem exists_threshold (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 ≤ (n : ℝ) ∧ 64 ≤ β ^ 2 * ρ ^ 4 * n ∧ 2 ≤ ρ ^ 4 * n := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (1 : ℝ) (max (64 / (β ^ 2 * ρ ^ 4)) (2 / ρ ^ 4)))
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hbig : max (1 : ℝ) (max (64 / (β ^ 2 * ρ ^ 4)) (2 / ρ ^ 4)) ≤ n :=
    hN.le.trans hNn
  obtain ⟨h1, h2, h3⟩ := (max_le_iff.mp hbig).imp_right max_le_iff.mp
  refine ⟨h1, ?_, ?_⟩
  · have h := (div_le_iff₀ (show 0 < β ^ 2 * ρ ^ 4 by positivity)).mp h2
    nlinarith [h]
  · have h := (div_le_iff₀ (show 0 < ρ ^ 4 by positivity)).mp h3
    nlinarith [h]

end PartitionedTriangleAbsorption.DegreeReserveBudgetStage115
