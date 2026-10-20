/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! Scalar hierarchy for the whole-library hub budget. This does not supply an embedding. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.CompressedHierarchyBudget

/-- A feasible small-density hierarchy pays the compressed hub estimate. -/
theorem small_hub_budget (η θ ρ n hub : ℝ)
    (hη : 0 < η) (hη1 : η ≤ 1) (hn : 0 < n)
    (hθ : 6000 * θ = η) (hρ : 4000 * ρ = η * θ)
    (hhub : θ * hub ≤ (660 * ρ + 330 * ρ * θ + 1452 * θ ^ 2) * n) :
    hub < η * n := by
  have ht : 0 < θ := by linarith
  have ht1 : θ ≤ 1 := by linarith
  have hr : 0 < ρ := by nlinarith [mul_pos hη ht]
  have hrt : ρ * θ ≤ ρ := by nlinarith
  have hsq : 6000 * θ ^ 2 = η * θ := by
    nlinarith [congrArg (fun x : ℝ => x * θ) hθ]
  have hcoef : 660 * ρ + 330 * ρ * θ + 1452 * θ ^ 2 < η * θ := by
    nlinarith [mul_pos hη ht, sq_nonneg θ]
  have hscaled := mul_lt_mul_of_pos_right hcoef hn
  nlinarith

/-- A dyadic hub count within a factor two of any prescribed scale. -/
theorem exists_dyadic_scale (x : ℝ) (hx : 1 ≤ x) :
    ∃ p : ℕ, (2 ^ p : ℝ) ≤ x ∧ x / 2 < (2 ^ p : ℝ) := by
  let m := ⌊x⌋₊
  have hm : 0 < m := Nat.floor_pos.mpr hx
  refine ⟨Nat.log 2 m, ?_, ?_⟩
  · have hpow := Nat.pow_log_le_self 2 (Nat.ne_of_gt hm)
    have hcast : (2 ^ Nat.log 2 m : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpow
    exact hcast.trans (Nat.floor_le (by linarith))
  · have hpow := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) m
    have hcast : (m : ℝ) + 1 ≤ (2 ^ (Nat.log 2 m + 1) : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hpow)
    have hxlt : x < (m : ℝ) + 1 := Nat.lt_floor_add_one x
    rw [pow_succ] at hcast
    linarith

/-- The same hierarchy also bounds edge mass, counted over all library pieces. -/
theorem small_library_mass (η θ ρ n mass : ℝ)
    (hη : 0 < η) (hn : 0 < n)
    (hθ : 6000 * θ = η) (hρ : 4000 * ρ = η * θ)
    (hmass : mass ≤ 214 * 57635 * (ρ / 2 + 2 * θ ^ 2) * n ^ 2) :
    mass < η ^ 2 * n ^ 2 := by
  have hsq : 6000 * θ ^ 2 = η * θ := by
    nlinarith [congrArg (fun x : ℝ => x * θ) hθ]
  have hsqη : 36000000 * θ ^ 2 = η ^ 2 := by
    nlinarith [congrArg (fun x : ℝ => x ^ 2) hθ]
  have hcoef : 214 * 57635 * (ρ / 2 + 2 * θ ^ 2) < η ^ 2 := by
    nlinarith [sq_pos_of_pos hη]
  exact hmass.trans_lt (mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hn))

end PartitionedTriangleAbsorption.CompressedHierarchyBudget
