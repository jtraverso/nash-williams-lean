/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1WeightedMarginStage187

/-! # Scalar budget for physical F1 root repair

The floor and ceiling are accounted for before invoking the root selector.
The constants can be fixed before the graph order is known.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1ConeBudgetStage188

theorem cone_budget (n M S : ℕ) (κ ξ ρ : ℝ)
    (hn : 0 < n) (hκ : 0 < κ) (hξ : 0 < ξ) (hρ : 0 < ρ)
    (hρκ : ρ ≤ κ) (hξρ : ξ ≤ ρ / 32) (hslack : 512 * ξ < κ * ρ)
    (hscale : 32 ≤ ρ * n) (hceil : 1 ≤ ξ * n)
    (hM : (M : ℝ) ≤ ξ * (n : ℝ) ^ 2 / 2)
    (hS : κ * n ≤ (S : ℝ)) :
    let d := ⌊ρ * n / 16⌋₊
    let K := ⌈ξ * n⌉₊
    0 < d ∧ d * (d + K) + 6 * M < d * S ∧
      (2 * (d + K) : ℕ) ≤ ρ * n / 4 := by
  dsimp
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hdhi : (⌊ρ * n / 16⌋₊ : ℝ) ≤ ρ * n / 16 := Nat.floor_le (by positivity)
  have hdlo : ρ * n / 32 ≤ (⌊ρ * n / 16⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (ρ * (n : ℝ) / 16)
    linarith
  have hK : (⌈ξ * n⌉₊ : ℝ) ≤ 2 * ξ * n := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ ξ * (n : ℝ) by positivity)
    linarith
  have hξn := mul_le_mul_of_nonneg_right hξρ hn'.le
  have hdk : (⌊ρ * n / 16⌋₊ : ℝ) + ⌈ξ * n⌉₊ ≤ ρ * n / 8 := by linarith
  have hprod := mul_le_mul hdhi hdk (by positivity) (by positivity)
  have hρn := mul_le_mul_of_nonneg_right hρκ (show 0 ≤ ρ * (n : ℝ) ^ 2 by positivity)
  have hMs := mul_lt_mul_of_pos_right hslack (sq_pos_of_pos hn')
  have hright := mul_le_mul hdlo hS (by positivity) (by positivity)
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, ?_⟩
  · have h : (⌊ρ * n / 16⌋₊ : ℝ) * ((⌊ρ * n / 16⌋₊ : ℝ) + ⌈ξ * n⌉₊) +
        6 * M < (⌊ρ * n / 16⌋₊ : ℝ) * S := by nlinarith
    exact_mod_cast h
  · push_cast
    linarith

theorem cone_parameters (κ ζ : ℝ) (hκ : 0 < κ) (hζ : 0 < ζ) :
    ∃ ξ ρ : ℝ, 0 < ξ ∧ 0 < ρ ∧ ρ ≤ κ ∧ ρ ≤ ζ ∧
      ξ ≤ ρ / 32 ∧ 512 * ξ < κ * ρ := by
  let ρ := min κ ζ
  let ξ := min (ρ / 64) (κ * ρ / 2048)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hξρ : ξ ≤ ρ / 64 := min_le_left _ _
  have hξκ : ξ ≤ κ * ρ / 2048 := min_le_right _ _
  refine ⟨ξ, ρ, hξ, hρ, min_le_left _ _, min_le_right _ _, by linarith, ?_⟩
  nlinarith [mul_pos hκ hρ]

theorem cone_threshold (ξ ρ : ℝ) (hξ : 0 < ξ) (hρ : 0 < ρ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n ∧ 32 ≤ ρ * n ∧ 1 ≤ ξ * n := by
  refine ⟨max 1 (max ⌈32 / ρ⌉₊ ⌈1 / ξ⌉₊), ?_⟩
  intro n hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnρ : ⌈32 / ρ⌉₊ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnξ : ⌈1 / ξ⌉₊ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hρn := (Nat.le_ceil (32 / ρ)).trans (show (⌈32 / ρ⌉₊ : ℝ) ≤ n by exact_mod_cast hnρ)
  have hξn := (Nat.le_ceil (1 / ξ)).trans (show (⌈1 / ξ⌉₊ : ℝ) ≤ n by exact_mod_cast hnξ)
  refine ⟨by omega, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_left hρn hρ.le
    rw [mul_div_cancel₀ _ hρ.ne'] at h
    linarith
  · have h := mul_le_mul_of_nonneg_left hξn hξ.le
    rw [mul_div_cancel₀ _ hξ.ne'] at h
    linarith

end PartitionedTriangleAbsorption.F1ConeBudgetStage188

