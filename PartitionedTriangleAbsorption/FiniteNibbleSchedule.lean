/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage14

/-! # Deterministic error and loss budgets for a finite physical nibble

These are consumers of explicit step inequalities, not a probabilistic producer.
The near-load round and its actual physical packing remain written proofs.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FiniteNibbleSchedule

theorem error_recurrence_le (a ε : ℝ) (ha : 1 ≤ a) (hε : 0 ≤ ε)
    (δ : ℕ → ℝ) (hzero : δ 0 ≤ 0)
    (hstep : ∀ j, δ (j + 1) ≤ a * δ j + 2 * ε) (j : ℕ) :
    δ j ≤ 2 * ε * (j : ℝ) * a ^ j := by
  induction j with
  | zero => simpa only [Nat.cast_zero, mul_zero, zero_mul] using hzero
  | succ j ih =>
    have ha0 : 0 ≤ a := by linarith
    have he : 0 ≤ 2 * ε := by positivity
    have hp : 1 ≤ a ^ (j + 1) := one_le_pow₀ ha
    calc
      δ (j + 1) ≤ a * δ j + 2 * ε := hstep j
      _ ≤ a * (2 * ε * (j : ℝ) * a ^ j) + 2 * ε :=
        add_le_add (mul_le_mul_of_nonneg_left ih ha0) (le_refl _)
      _ = 2 * ε * (j : ℝ) * a ^ (j + 1) + 2 * ε := by rw [pow_succ]; ring
      _ ≤ 2 * ε * (j : ℝ) * a ^ (j + 1) + 2 * ε * a ^ (j + 1) :=
        add_le_add (le_refl _)
          (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hp he)
      _ = 2 * ε * ((j + 1 : ℕ) : ℝ) * a ^ (j + 1) := by push_cast; ring

theorem error_budget_mono (a ε : ℝ) (ha : 1 ≤ a) (hε : 0 ≤ ε)
    {j r : ℕ} (hjr : j ≤ r) :
    2 * ε * (j : ℝ) * a ^ j ≤ 2 * ε * (r : ℝ) * a ^ r := by
  have ha0 : 0 ≤ a := by linarith
  have hcast : (j : ℝ) ≤ r := by exact_mod_cast hjr
  have hp : a ^ j ≤ a ^ r := pow_le_pow_right₀ ha hjr
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_left hcast (by positivity)
  · exact hp
  · exact pow_nonneg ha0 _
  · positivity

theorem finite_error_le (a ε bound : ℝ) (ha : 1 ≤ a) (hε : 0 ≤ ε)
    (δ : ℕ → ℝ) (hzero : δ 0 ≤ 0)
    (hstep : ∀ j, δ (j + 1) ≤ a * δ j + 2 * ε)
    {j r : ℕ} (hjr : j ≤ r) (hbudget : 2 * ε * (r : ℝ) * a ^ r ≤ bound) :
    δ j ≤ bound :=
  (error_recurrence_le a ε ha hε δ hzero hstep j).trans
    ((error_budget_mono a ε ha hε hjr).trans hbudget)

theorem cumulative_waste_le (γ η scale : ℝ) (hγ : 0 ≤ γ) (hγ8 : γ ≤ 8)
    (hbudget : 768 * γ * (scale + 1) ≤ η)
    (r : ℕ) (hrounds : (r : ℝ) * γ ≤ 8 * scale + γ) :
    24 * (r : ℝ) * γ ^ 2 ≤ η / 4 := by
  have h1 := mul_le_mul_of_nonneg_right hrounds (show 0 ≤ 24 * γ by positivity)
  have h2 : 24 * γ ^ 2 ≤ 192 * γ := by nlinarith
  nlinarith

end PartitionedTriangleAbsorption.FiniteNibbleSchedule
