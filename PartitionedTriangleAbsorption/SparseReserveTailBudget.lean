/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # The explicit sparse-reserve union-bound budget

The exponential lower bounds are proved from Mathlib's power-series estimate,
not assumed as scalar premises. This module bounds the sum of the prospective
Hoeffding tails; it does not assume those tails describe an actual sample.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SparseReserveTailBudget

theorem failure_budget (n c prob types : ℝ) (hn : 0 < n) (hc : 0 ≤ c)
    (hcherries : 72 * types ≤ c ^ 3 * n) (hdegrees : 2 ≤ prob ^ 4 * n) :
    6 * types * n ^ 2 * Real.exp (-(c * n)) +
      n * Real.exp (-(2 * prob ^ 2 * n)) ≤ 3 / 4 := by
  have hpow3 := Real.pow_div_factorial_le_exp (c * n) (mul_nonneg hc hn.le) 3
  have hpow2 := Real.pow_div_factorial_le_exp (2 * prob ^ 2 * n)
    (show 0 ≤ 2 * prob ^ 2 * n by positivity) 2
  norm_num at hpow3 hpow2
  have hch := mul_le_mul_of_nonneg_right hcherries (sq_nonneg n)
  have hdeg := mul_le_mul_of_nonneg_right hdegrees (show 0 ≤ 2 * n by positivity)
  have hE1 : 12 * types * n ^ 2 ≤ Real.exp (c * n) := by nlinarith [hpow3, hch]
  have hE2 : 4 * n ≤ Real.exp (2 * prob ^ 2 * n) := by nlinarith [hpow2, hdeg]
  have htail1 : 6 * types * n ^ 2 / Real.exp (c * n) ≤ 1 / 2 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  have htail2 : n / Real.exp (2 * prob ^ 2 * n) ≤ 1 / 4 := by
    apply (div_le_iff₀ (Real.exp_pos _)).mpr
    linarith
  simp only [Real.exp_neg, ← div_eq_mul_inv]
  linarith

/-- The explicit threshold stated in the feedback, written without division.
The missing probabilistic step is not hidden in an assumed scalar tail. -/
theorem explicit_threshold (n α prob types : ℝ) (hn : 0 < n) (hα : 0 ≤ α)
    (hsize : 576 * types ≤ α ^ 3 * prob ^ 12 * n)
    (hdegrees : 2 ≤ prob ^ 4 * n) :
    6 * types * n ^ 2 * Real.exp (-(α * prob ^ 4 / 2 * n)) +
      n * Real.exp (-(2 * prob ^ 2 * n)) ≤ 3 / 4 := by
  apply failure_budget n (α * prob ^ 4 / 2) prob types hn (by positivity)
    (by nlinarith [hsize]) hdegrees

end PartitionedTriangleAbsorption.SparseReserveTailBudget
