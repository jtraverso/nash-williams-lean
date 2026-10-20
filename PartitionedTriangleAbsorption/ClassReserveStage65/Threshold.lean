/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Order.Filter.AtTopBot.Archimedean

/-! # One uniform order threshold for the class-aware reserve

`failureBudget γ ρ n` is the total union-bound budget used by the reserve producer:

* `n` vertex-degree upper tails, each at most `exp (-(2 ρ² n))`;
* `n⁴` marker lower tails (one for each ordered root tuple `(a, b, w, z)`), each at most
  `exp (-((ρ³)² (γ n / 2) / 2))`;
* `(2ⁿ)²` cross-edge lower tails (one for each pair of vertex sets), each at most
  `exp (-(ρ² m² / 2))` with `m = ρ³ (γ n / 2) / 2`.

`exists_uniform_threshold` chooses `N` from `γ, ρ` alone.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassReserveStage65

open Filter Topology

/-- The guaranteed size of a marked set: `ρ³ · (γ n / 2) / 2 = γ ρ³ n / 4`. -/
noncomputable def markBound (γ ρ : ℝ) (n : ℕ) : ℝ := ρ ^ 3 * (γ * n / 2) / 2

/-- Total failure budget of the union bound. -/
noncomputable def failureBudget (γ ρ : ℝ) (n : ℕ) : ℝ :=
  n * Real.exp (-(2 * ρ ^ 2 * n)) +
    (n : ℝ) ^ 4 * Real.exp (-(ρ ^ 3) ^ 2 * (γ * n / 2) / 2) +
    ((2 : ℝ) ^ n) ^ 2 * Real.exp (-ρ ^ 2 * (markBound γ ρ n * markBound γ ρ n) / 2)

theorem tendsto_pow_mul_exp_neg (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ k * Real.exp (-(c * n))) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) c hc).comp
    tendsto_natCast_atTop_atTop
  refine h.congr (fun n => ?_)
  simp [Real.rpow_natCast, neg_mul]

theorem tendsto_four_pow_mul_exp_neg (d : ℝ) (hd : 0 < d) :
    Tendsto (fun n : ℕ => ((2 : ℝ) ^ n) ^ 2 * Real.exp (-(d * n ^ 2))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
  · exact Eventually.of_forall (fun n => by positivity)
  · obtain ⟨M, hM⟩ := exists_nat_gt (3 / d)
    filter_upwards [eventually_ge_atTop M] with n hn
    have hnM : (M : ℝ) ≤ n := by exact_mod_cast hn
    have h3 : 3 ≤ d * n := by
      have := (div_lt_iff₀ hd).mp (hM.trans_le hnM); linarith
    have h2 : ((2 : ℝ) ^ n) ^ 2 ≤ Real.exp (2 * n) := by
      have he : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); linarith
      calc ((2 : ℝ) ^ n) ^ 2 ≤ (Real.exp 1 ^ n) ^ 2 := by gcongr
        _ = Real.exp (2 * n) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; push_cast; ring_nf
    calc ((2 : ℝ) ^ n) ^ 2 * Real.exp (-(d * n ^ 2))
        ≤ Real.exp (2 * n) * Real.exp (-(d * n ^ 2)) := by gcongr
      _ = Real.exp (2 * n - d * n ^ 2) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(n : ℝ)) := by
          apply Real.exp_le_exp.mpr
          have : (0 : ℝ) ≤ n := by positivity
          nlinarith

theorem tendsto_failureBudget (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) :
    Tendsto (failureBudget γ ρ) atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_exp_neg (2 * ρ ^ 2) (by positivity) 1
  have h2 := tendsto_pow_mul_exp_neg ((ρ ^ 3) ^ 2 * γ / 4) (by positivity) 4
  have h3 := tendsto_four_pow_mul_exp_neg (ρ ^ 2 * (ρ ^ 3 * γ / 4) ^ 2 / 2) (by positivity)
  have h := (h1.add h2).add h3
  simp only [add_zero] at h
  refine h.congr (fun n => ?_)
  simp only [failureBudget, markBound, pow_one]
  congr 3
  · ring_nf
  · ring_nf

/-- **Uniform threshold.** `N` depends only on `γ` and `ρ`. -/
theorem exists_uniform_threshold (γ ρ : ℝ) (hγ : 0 < γ) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 2 ≤ γ * n ∧ failureBudget γ ρ n < 1 := by
  have hev : ∀ᶠ n : ℕ in atTop, failureBudget γ ρ n < 1 :=
    (tendsto_failureBudget γ ρ hγ hρ).eventually (gt_mem_nhds one_pos)
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp hev
  obtain ⟨N2, hN2⟩ := exists_nat_gt (2 / γ)
  refine ⟨max N1 N2, fun n hn => ⟨?_, hN1 n ((le_max_left _ _).trans hn)⟩⟩
  have hn2 : (N2 : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have := (div_lt_iff₀ hγ).mp (hN2.trans_le hn2)
  linarith

end PartitionedTriangleAbsorption.ClassReserveStage65
