/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! # Corrected scalar budgets for the ordinary refiner

These are the two refiner budgets and the four-root exclusion budget previously
checked with Certo. They do not assume the existence of a refiner or private absorber.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RefinerConstructionBudget

theorem physical_budget (lam rho : ℝ) (hlam : 0 < lam)
    (hsmall : lam ≤ 1 / 64) (hrho : 0 ≤ rho)
    (hscale : 16777216 * rho ≤ lam * lam) :
    65536 * rho + 4 * rho * lam + (97 / 16) * lam * lam < lam / 2 := by
  have hsquare : lam * lam ≤ lam / 64 := by nlinarith
  have hproduct : rho * lam ≤ rho / 64 := by nlinarith
  nlinarith

theorem library_incidence_budget (lam rho : ℝ) (hlam : 0 ≤ lam)
    (hsmall : lam ≤ 1 / 64) (hscale : 16777216 * rho ≤ lam * lam) :
    3600 * lam + 2304 * rho ≤ 4096 * lam := by
  have hsquare : lam * lam ≤ lam / 64 := by nlinarith
  linarith

/-- The actual quotient budget used by the physical path-family selection theorem. -/
theorem physical_family_budget (lam rho n M d r q : ℝ) (hlam : 0 < lam)
    (hsmall : lam ≤ 1 / 64) (hrho : 0 ≤ rho)
    (hscale : 16777216 * rho ≤ lam * lam) (hn : 0 < n)
    (hM : M ≤ 512 * rho * n ^ 2) (hd : d ≤ 2 * rho * n)
    (hr : r ≤ 3 * lam * n) (hqlo : lam * n / 128 ≤ q)
    (hqhi : q ≤ lam * n / 64) :
    M / q + 2 * (d + r + 2 * q) < n / 2 := by
  have hden : 0 < lam * n / 128 := by positivity
  have hq : 0 < q := hden.trans_le hqlo
  have hmnon : 0 ≤ 512 * rho * n ^ 2 := by positivity
  have hratio : M / q ≤ (65536 * rho / lam) * n := by
    calc
      M / q ≤ (512 * rho * n ^ 2) / q := div_le_div_of_nonneg_right hM hq.le
      _ ≤ (512 * rho * n ^ 2) / (lam * n / 128) :=
        div_le_div_of_nonneg_left hmnon hden hqlo
      _ = _ := by field_simp; ring
  have hpol := physical_budget lam rho hlam hsmall hrho hscale
  have hnormalized : 65536 * rho / lam + 4 * rho + (97 / 16) * lam < 1 / 2 := by
    have hcancel : (65536 * rho / lam) * lam = 65536 * rho :=
      div_mul_cancel₀ _ hlam.ne'
    nlinarith
  have hscaled := mul_lt_mul_of_pos_right hnormalized hn
  nlinarith

theorem library_size_budget (S N rho n : ℝ) (hn : 1 ≤ rho * n * n)
    (hS : S ≤ 2 * rho * n * n) (hN : N ≤ 33 * S + 2) :
    N ≤ 68 * rho * n * n := by linarith

theorem final_library_size_budget (N pieces rho n : ℝ)
    (hN : N ≤ 68 * rho * n * n) (hpieces : pieces ≤ 18 * N) :
    pieces ≤ 1224 * rho * n * n := by linarith

theorem private_exclusion_budget (eps forbidden incidence auxiliary saturated injection : ℝ)
    (heps : 0 < eps) (hf : 32 * forbidden ≤ eps)
    (hi : 512 * incidence ≤ eps) (ha : 16 * auxiliary ≤ eps)
    (hs : 8 * saturated ≤ eps) (hj : 4 * injection ≤ eps) :
    4 * (forbidden + 4 * incidence + auxiliary) + saturated + injection < 4 * eps := by
  linarith

end PartitionedTriangleAbsorption.RefinerConstructionBudget
