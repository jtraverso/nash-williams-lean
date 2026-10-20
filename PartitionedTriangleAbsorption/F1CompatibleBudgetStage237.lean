/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1GraphReserveStage234

/-! # Compatible scalar budgets for the corrected F1 level

This checks a single hierarchy, including inherited damage, charge repair,
sampled-grandchild interference, pair overlap, apex supply and next-level
load. The geometric estimates must still be proved for one physical level;
these inequalities do not assert existence of that level.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1CompatibleBudgetStage237

open Filter Topology

/-- Coefficients are normalized by the current order (quadratically for
charge and pool sizes). Strict slack leaves room for integer rounding and
the logarithmic term of the spread lemma at sufficiently large order. -/
def Compatible (β ρ ζ ε η κ σ δ : ℝ) : Prop :=
  0 < β ∧ β ≤ 1 / 1000000 ∧ 0 < ρ ∧ ρ < 1 / 2 ∧
  0 < ζ ∧ 0 < ε ∧ 0 < η ∧ 0 < κ ∧ 0 < σ ∧
  σ = β / 128 ∧ δ = 6 * κ / σ ∧ 2 * κ < σ ∧
  -- Available boundary pools: child classes minus missing/reserved edges.
  ε + ζ + ρ + ε < β / 16 ∧
  -- Actual charge ledger, including the inherited damaged boundary.
  9 * ε + 6 * ρ * ε + 2 * ρ * ζ * β < κ ∧
  -- All four cover-down margins, using sampled rather than total bad sets.
  8 * (ρ * (ε + β) * β + δ + ε + η + 2 * (ρ * β / 10000)) +
    3 * (2 * ρ * ε * β + ρ * ζ + δ + ε + η) + 2 * η < ρ * β / 8 ∧
  -- Pair overlaps, including perturbations from correction and leftover.
  8 * (ρ ^ 2 * β + ε + 2 * δ + 2 * η) * ρ / (ρ * β / 10000) <
    (ρ * β / 10000) / 4 ∧
  -- Apex allocation; a floor loses at most a factor of two.
  2 * η + 200 * η / ρ < (ρ ^ 2 * β / 32) / 2 ∧
  -- Visits, including apex use, fit inside the next damage budget.
  ρ + ε + δ + η + 2 * (ρ / 100) < 2 * ρ ∧
  2 * ρ < ζ * β / 2 ∧
  -- Damage including deletion of the protected child and padding.
  β + ζ + 2 * ρ + δ + 16 * ε < 1 / 2560

/-- A concrete rational witness: no cyclic hierarchy of small constants. -/
theorem exists_compatible : ∃ β ρ ζ ε η κ σ δ : ℝ, Compatible β ρ ζ ε η κ σ δ := by
  let β : ℝ := 1 / 10 ^ 6
  let ρ : ℝ := 1 / 10 ^ 40
  let ζ : ℝ := 16 * ρ / β
  let ε : ℝ := 1 / 10 ^ 180
  let κ : ℝ := 8 * ρ * ζ * β
  let σ : ℝ := β / 128
  exact ⟨β, ρ, ζ, ε, ε, κ, σ, 6 * κ / σ, by
    norm_num [Compatible, β, ρ, ζ, ε, κ, σ]⟩

/-- A quadratic charge bound with strict coefficient slack pays the extra
unit needed by the integral correction, uniformly above a fixed threshold. -/
theorem charge_rounding_threshold (a κ : ℝ) (ha : a < κ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → a * (n : ℝ) ^ 2 + 1 ≤ κ * (n : ℝ) ^ 2 := by
  refine ⟨max 1 ⌈1 / (κ - a)⌉₊, ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hh : 1 / (κ - a) ≤ (n : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hn)
  have hpos : 0 < κ - a := by linarith
  have hmul := (div_le_iff₀ hpos).mp hh
  have hsq : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left hsq hpos.le
  nlinarith

/-- Polynomially many simultaneous local tests have one threshold. The
additional constant term pays the two global charge-count queries. -/
theorem joint_query_threshold (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (32 * (n : ℝ) ^ 3 + 2) * (2 * Real.exp (-(2 * ε ^ 2) * n)) < 1 := by
  have h1 := (ClassReserveStage65.tendsto_pow_mul_exp_neg
    (2 * ε ^ 2) (by positivity) 3).const_mul 64
  have h2 := (ClassReserveStage65.tendsto_pow_mul_exp_neg
    (2 * ε ^ 2) (by positivity) 0).const_mul 4
  have h := h1.add h2
  simp only [mul_zero, add_zero] at h
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num)))
  refine ⟨N, fun n hn => ?_⟩
  convert hN n hn using 1
  ring_nf

/-- Three approximately equal class counts satisfy the four integer margins
once their common scale dominates the aggregate error. -/
theorem margins_from_counts (a b c Γ γ : ℕ) (m e : ℝ)
    (ha : m - e ≤ a) (ha' : (a : ℝ) ≤ m + e)
    (hb : m - e ≤ b) (hc : m - e ≤ c)
    (hmargin : 8 * (Γ : ℝ) + 1 + 2 * γ + 3 * e ≤ m) :
    4 * Γ + 1 + γ ≤ a ∧ 6 * Γ + 1 + γ ≤ b ∧
      6 * Γ + 1 + γ ≤ c ∧ a + 8 * Γ + 1 + 2 * γ ≤ b + c := by
  have hΓ : (0 : ℝ) ≤ Γ := Nat.cast_nonneg _
  have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
  have h1 : 4 * (Γ : ℝ) + 1 + γ ≤ a := by linarith
  have h2 : 6 * (Γ : ℝ) + 1 + γ ≤ b := by linarith
  have h3 : 6 * (Γ : ℝ) + 1 + γ ≤ c := by linarith
  have h4 : (a : ℝ) + 8 * Γ + 1 + 2 * γ ≤ b + c := by linarith
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2,
    by exact_mod_cast h3, by exact_mod_cast h4⟩

end PartitionedTriangleAbsorption.F1CompatibleBudgetStage237
