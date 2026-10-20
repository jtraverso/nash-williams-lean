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
public import Mathlib.Data.Nat.Cast.Order.Field

/-! # Scalar budgets of the structural refiner

The parameter hierarchy is `γ ≥ 32λ`, `λ ≤ 1/64`, `2^42 ρ ≤ λ²`, `λn ≥ 256`, `ρn ≥ 1`.
`token_budget_real` is the strict selection budget of one physical token layer and
`token_root_real` its root-load condition, for at most `2^32 ρ n²` token identities.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3

theorem token_budget_real (N q r d n γ lam rho : ℝ) (hlam : 0 < lam) (hlamγ : 32 * lam ≤ γ)
    (hrho : 0 ≤ rho) (hscale : 2 ^ 42 * rho ≤ lam ^ 2) (hn : 0 < n)
    (hN : N ≤ 2 ^ 32 * rho * n ^ 2) (hqlo : lam * n / 128 ≤ q) (hqhi : q ≤ lam * n / 64)
    (hr : r ≤ lam * n) (hd : d ≤ 6 * lam * n) :
    4 * N / q + 2 * (d + r + 2 * q) < γ * n := by
  have hden : 0 < lam * n / 128 := by positivity
  have hq : 0 < q := hden.trans_le hqlo
  have hmnon : 0 ≤ 4 * (2 ^ 32 * rho * n ^ 2) := by positivity
  have h1 : 4 * N / q ≤ 4 * (2 ^ 32 * rho * n ^ 2) / (lam * n / 128) := by
    calc 4 * N / q ≤ 4 * (2 ^ 32 * rho * n ^ 2) / q :=
          div_le_div_of_nonneg_right (by linarith) hq.le
      _ ≤ 4 * (2 ^ 32 * rho * n ^ 2) / (lam * n / 128) :=
          div_le_div_of_nonneg_left hmnon hden hqlo
  have h2 : 4 * (2 ^ 32 * rho * n ^ 2) / (lam * n / 128) = (2 ^ 41 * rho / lam) * n := by
    field_simp; ring
  have h3 : 2 ^ 41 * rho / lam ≤ lam / 2 := by
    rw [div_le_iff₀ hlam]; nlinarith
  have h4 : (2 ^ 41 * rho / lam) * n ≤ lam / 2 * n := mul_le_mul_of_nonneg_right h3 hn.le
  have h5 : 0 < lam * n := by positivity
  have h6 : 32 * lam * n ≤ γ * n := mul_le_mul_of_nonneg_right hlamγ hn.le
  nlinarith

theorem token_root_real (N c n γ lam rho : ℝ) (hlam : 0 < lam) (hlamγ : 32 * lam ≤ γ)
    (hrho : 0 ≤ rho) (hscale : 2 ^ 42 * rho ≤ lam ^ 2) (hn : 0 < n) (hn2 : 256 ≤ lam * n)
    (hN : N ≤ 2 ^ 32 * rho * n ^ 2) (hc : γ * n ≤ c) :
    4 * (2 * N / c + 1) ≤ lam * n - 1 := by
  have hγ : 0 < γ := by linarith
  have hγn : 0 < γ * n := by positivity
  have hc0 : 0 < c := hγn.trans_le hc
  have h1 : 2 * N / c ≤ 2 * (2 ^ 32 * rho * n ^ 2) / (γ * n) := by
    calc 2 * N / c ≤ 2 * (2 ^ 32 * rho * n ^ 2) / c :=
          div_le_div_of_nonneg_right (by linarith) hc0.le
      _ ≤ 2 * (2 ^ 32 * rho * n ^ 2) / (γ * n) :=
          div_le_div_of_nonneg_left (by positivity) hγn hc
  have h2 : 2 * (2 ^ 32 * rho * n ^ 2) / (γ * n) ≤ lam * n / 4096 := by
    rw [div_le_iff₀ hγn]
    have : 2 ^ 33 * rho * 4096 ≤ lam * γ := by nlinarith
    nlinarith
  linarith

end PartitionedTriangleAbsorption.StructuralF3
