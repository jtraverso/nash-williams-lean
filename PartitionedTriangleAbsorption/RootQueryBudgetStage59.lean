/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SparseReserveTailBudget
public import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Uniform scalar thresholds for four-root reserve queries

The fifth-order exponential-series bound dominates the fourth-order query
count. All constants are coarse; no optimality or geometric hypothesis is
inferred from these scalar inequalities.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQueryBudgetStage59

theorem failure_budget_four (n c ρ : ℝ) (hn : 1 ≤ n) (hc : 0 ≤ c)
    (hsize : 38400 ≤ c ^ 5 * n) (hdegrees : 2 ≤ ρ ^ 4 * n) :
    n * Real.exp (-(2 * ρ ^ 2 * n)) +
      10 * (n + 1) ^ 4 * Real.exp (-(c * n)) ≤ 3 / 4 := by
  have hn0 : 0 ≤ n := by linarith
  have hpow5 := Real.pow_div_factorial_le_exp (c * n) (mul_nonneg hc hn0) 5
  have hpow2 := Real.pow_div_factorial_le_exp (2 * ρ ^ 2 * n)
    (show 0 ≤ 2 * ρ ^ 2 * n by positivity) 2
  norm_num [mul_pow] at hpow5 hpow2
  have hs := mul_le_mul_of_nonneg_right hsize (show 0 ≤ n ^ 4 by positivity)
  have hd := mul_le_mul_of_nonneg_right hdegrees (show 0 ≤ 2 * n by positivity)
  have hE1 : 320 * n ^ 4 ≤ Real.exp (c * n) := by nlinarith
  have hE2 : 4 * n ≤ Real.exp (2 * ρ ^ 2 * n) := by nlinarith
  have hp : (n + 1) ^ 4 ≤ (2 * n) ^ 4 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 4
  have hquery : 10 * (n + 1) ^ 4 ≤ 160 * n ^ 4 := by nlinarith
  have ht1 : 10 * (n + 1) ^ 4 / Real.exp (c * n) ≤ 1 / 2 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have ht2 : n / Real.exp (2 * ρ ^ 2 * n) ≤ 1 / 4 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  simp only [Real.exp_neg, ← div_eq_mul_inv]
  linarith

theorem explicit_four_root_budget (n β ρ : ℝ) (hn : 1 ≤ n) (hβ : 0 ≤ β)
    (hsize : 1228800 ≤ β ^ 5 * ρ ^ 40 * n) (hdegrees : 2 ≤ ρ ^ 4 * n) :
    n * Real.exp (-2 * ρ ^ 2 * n) +
      10 * (n + 1) ^ 4 * Real.exp (-(ρ ^ 4) ^ 2 * β * n / 2) ≤ 3 / 4 := by
  have hb := failure_budget_four n ((ρ ^ 4) ^ 2 * β / 2) ρ hn
    (by positivity) (by nlinarith [hsize]) hdegrees
  have he : -((ρ ^ 4) ^ 2 * β / 2 * n) = -(ρ ^ 4) ^ 2 * β * n / 2 := by ring
  simpa only [he, neg_mul] using hb

/-- This order threshold is chosen using only the two real parameters. -/
theorem exists_uniform_threshold (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      1 ≤ (n : ℝ) ∧ 1228800 ≤ β ^ 5 * ρ ^ 40 * n ∧ 2 ≤ ρ ^ 4 * n := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (1 : ℝ) (max (1228800 / (β ^ 5 * ρ ^ 40)) (2 / ρ ^ 4)))
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hbig : max (1 : ℝ) (max (1228800 / (β ^ 5 * ρ ^ 40)) (2 / ρ ^ 4)) ≤ n :=
    hN.le.trans hNn
  obtain ⟨h1, h2, h3⟩ := (max_le_iff.mp hbig).imp_right max_le_iff.mp
  refine ⟨h1, ?_, ?_⟩
  · have h := (div_le_iff₀ (show 0 < β ^ 5 * ρ ^ 40 by positivity)).mp h2
    nlinarith [h]
  · have h := (div_le_iff₀ (show 0 < ρ ^ 4 by positivity)).mp h3
    nlinarith [h]

end PartitionedTriangleAbsorption.RootQueryBudgetStage59
