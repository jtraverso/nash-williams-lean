/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

@[expose] public section

/-! Absolute bounds for the small star monitors omitted by the protected nibble. -/

namespace NashWilliams18.Case124.BoundedCore

/-- A conservative explicit threshold pays the fourth-root monitor cutoff. -/
theorem quarter_cutoff_le_linear {a n : ℝ} (ha : 0 < a) (hn : 1 ≤ n)
    (hlarge : (6 / a) ^ 2 ≤ n) :
    6 * n ^ ((1 : ℝ) / 4) ≤ a * n := by
  have hroot : 6 / a ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hlarge
  have hpay : 6 ≤ a * Real.sqrt n := by
    have := (div_le_iff₀ ha).mp hroot
    nlinarith
  have hquarter : n ^ ((1 : ℝ) / 4) ≤ Real.sqrt n := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn (by norm_num)
  have hmul := mul_le_mul_of_nonneg_right hpay (Real.sqrt_nonneg n)
  have hsquare := Real.sq_sqrt (show 0 ≤ n by linarith)
  nlinarith

/-- The cutoff threshold is chosen before the ambient graph/order. -/
theorem exists_quarter_cutoff (a : ℝ) (ha : 0 < a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      6 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ a * n := by
  refine ⟨max 1 ⌈(6 / a) ^ 2⌉₊, fun n hn => ?_⟩
  apply quarter_cutoff_le_linear ha
  · exact_mod_cast le_trans (le_max_left _ _) hn
  · exact (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hn)

/-- Large monitors use the nibble estimate; small ones use their entire cardinality. -/
theorem residual_of_monitor {n d r : ℕ} {a : ℝ} (ha : 0 ≤ a)
    (hr : r ≤ d) (hd : d ≤ n)
    (hcut : 6 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ a * n)
    (hmon : 6 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ d → (r : ℝ) ≤ a * d) :
    (r : ℝ) ≤ a * n := by
  by_cases h : 6 * (n : ℝ) ^ ((1 : ℝ) / 4) ≤ d
  · exact (hmon h).trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hd) ha)
  · have hdcut : (d : ℝ) < 6 * (n : ℝ) ^ ((1 : ℝ) / 4) := lt_of_not_ge h
    exact (show (r : ℝ) ≤ d by exact_mod_cast hr).trans (hdcut.le.trans hcut)

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.quarter_cutoff_le_linear
#print axioms NashWilliams18.Case124.BoundedCore.exists_quarter_cutoff
#print axioms NashWilliams18.Case124.BoundedCore.residual_of_monitor
