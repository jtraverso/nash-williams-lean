/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib

/-!
# Scalar budgets of the protected round

All constants of the round are explicit functions of the child scale `q`:

* `κ = q / 1000` (damage and output degree scale);
* `ρ = q² / 4000` (radial reserve probability; `ρ = κ q / 4`);
* `σ = ρ⁴ q² / 10⁴` (sampling error and nibble leftover scale).

The lemmas below are the scalar inequalities used by `roundUnivSpec124_holds`; each takes the
actual real bounds on the rounded natural numbers as hypotheses.
-/

namespace NashWilliams18.Case124.BoundedCore.RoundConst

/-- `ρ ≤ q / 400000` for `q ≤ 1/100`. -/
lemma rho_le {q ρ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 100) (hρ : ρ = q ^ 2 / 4000) :
    ρ ≤ q / 400000 := by
  rw [hρ]; nlinarith

lemma rho_pos {q ρ : ℝ} (hq : 0 < q) (hρ : ρ = q ^ 2 / 4000) : 0 < ρ := by
  rw [hρ]; positivity

/-- `σ ≤ ρ q / 10⁴`. -/
lemma sig_le {q ρ σ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 100) (hρ : ρ = q ^ 2 / 4000)
    (hσ : σ = ρ ^ 4 * q ^ 2 / 10 ^ 4) : σ ≤ ρ * q / 10 ^ 4 := by
  have hr0 := rho_pos hq hρ
  have hr1 := rho_le hq hq1 hρ
  have hr1' : ρ ≤ 1 := by linarith
  have h3 : ρ ^ 3 * q ≤ 1 := by
    have : ρ ^ 3 ≤ 1 := pow_le_one₀ hr0.le hr1'
    nlinarith
  rw [hσ]
  have : ρ ^ 4 * q ^ 2 = (ρ * q) * (ρ ^ 3 * q) := by ring
  rw [this]
  have hrq : 0 ≤ ρ * q := by positivity
  have := mul_le_mul_of_nonneg_left h3 hrq
  linarith

/-- `4 σ ≤ ρ² · (7 q / 8)`, i.e. four sampling errors fit below the apex scale. -/
lemma four_sig_le {q ρ σ : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 100) (hρ : ρ = q ^ 2 / 4000)
    (hσ : σ = ρ ^ 4 * q ^ 2 / 10 ^ 4) : 4 * σ ≤ ρ ^ 2 * (7 * q / 8) / 100 := by
  have hr0 := rho_pos hq hρ
  have hr1 := rho_le hq hq1 hρ
  have hr1' : ρ ≤ 1 := by linarith
  have h2 : ρ ^ 2 * q ≤ 1 := by
    have : ρ ^ 2 ≤ 1 := pow_le_one₀ hr0.le hr1'
    nlinarith
  rw [hσ]
  have : 4 * (ρ ^ 4 * q ^ 2 / 10 ^ 4) = (ρ ^ 2 * q) * (4 * (ρ ^ 2 * q) / 10 ^ 4) := by ring
  rw [this]
  have hrq : 0 ≤ ρ ^ 2 * q := by positivity
  have : 4 * (ρ ^ 2 * q) / 10 ^ 4 ≤ 7 / 800 := by nlinarith
  have := mul_le_mul_of_nonneg_left this hrq
  nlinarith

/-- **Dirac margin.** -/
lemma marg_bound {q ρ θ n u z ε D γ B K lg : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1 / 100) (hρ : ρ = q ^ 2 / 4000)
    (hθ : θ ≤ 1 / 100) (hn : 0 ≤ n) (hu : 7 * q / 8 * n ≤ u)
    (hz0 : 0 ≤ z) (hz : z ≤ 9 * q / 8 * u)
    (hε : ε ≤ ρ * q / 10 ^ 4) (hD : D ≤ ρ * q / 10 ^ 4 * n)
    (hγ : γ ≤ ρ * (1 / 4 + θ) * u + 2 * (ε * n) + D + 2)
    (hK : K ≤ 800 * ρ ^ 2 * n + 1)
    (hB : B ≤ ρ * u / 100 + 2 * lg + 1)
    (hlog : 4 * lg + 8 ≤ ρ * q * n / 20) :
    2 * (γ + B + K) ≤ ρ * ((3 / 4 - θ) * u - z - q / 1000 * n) - ε * n - D := by
  have hr0 := rho_pos hq hρ
  have hr1 := rho_le hq hq1 hρ
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hP : ρ * (7 * q / 8 * n) ≤ ρ * u := mul_le_mul_of_nonneg_left hu hr0.le
  have hθu : ρ * θ * u ≤ ρ * u / 100 := by
    have := mul_le_mul_of_nonneg_left hθ (mul_nonneg hr0.le hu0)
    nlinarith
  have hzu : ρ * z ≤ 9 / 800 * (ρ * u) := by
    have h1 : z ≤ 9 / 800 * u := by nlinarith
    nlinarith
  have hεn : ε * n ≤ ρ * q * n / 10 ^ 4 := by
    have := mul_le_mul_of_nonneg_right hε hn
    linarith
  have hr2 : ρ ^ 2 * n ≤ ρ * q * n / 400000 := by
    have := mul_le_mul_of_nonneg_left hr1 (mul_nonneg hr0.le hn)
    nlinarith
  nlinarith

/-- **Potential term** `(e - 1) ω Lv / K ≤ ρ u / 100`. -/
lemma potential_bound {ρ n u ω Lv K : ℝ} (hρ : 0 < ρ) (hn : 0 < n) (hu : 0 ≤ u)
    (hω0 : 0 ≤ ω) (hω : ω ≤ 2 * ρ ^ 2 * u) (hL0 : 0 ≤ Lv) (hL : Lv ≤ 2 * ρ * n)
    (hK : 800 * ρ ^ 2 * n ≤ K) :
    (Real.exp 1 - 1) * ω * Lv / K ≤ ρ * u / 100 := by
  have hKpos : 0 < K := lt_of_lt_of_le (by positivity) hK
  rw [div_le_iff₀ hKpos]
  have he : Real.exp 1 - 1 ≤ 2 := by linarith [Real.exp_one_lt_d9]
  have he0 : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h1 : (Real.exp 1 - 1) * ω * Lv ≤ 2 * (2 * ρ ^ 2 * u) * (2 * ρ * n) := by
    apply mul_le_mul (mul_le_mul he hω hω0 (by norm_num)) hL hL0 (by positivity)
  have h2 : ρ * u / 100 * (800 * ρ ^ 2 * n) ≤ ρ * u / 100 * K :=
    mul_le_mul_of_nonneg_left hK (by positivity)
  nlinarith

/-- **Greedy apex inequality** in real form. -/
lemma greedy_bound {q ρ σ n u D Kg M : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1 / 100) (hρ : ρ = q ^ 2 / 4000)
    (hσ : σ = ρ ^ 4 * q ^ 2 / 10 ^ 4) (hn : 0 < n) (hu : 7 * q / 8 * n ≤ u)
    (hσn : 1 ≤ σ * n)
    (hD : D ≤ σ * n)
    (hKg1 : ρ ^ 2 * u / 40 - 1 ≤ Kg) (hKg2 : Kg ≤ ρ ^ 2 * u / 40)
    (hM : 44 / 100 * (ρ ^ 2 * u) - 1 ≤ M) :
    3 * (n * D) + 12 * (Kg * (Kg + D)) < 2 * (Kg * M) := by
  have hr0 := rho_pos hq hρ
  have h4 := four_sig_le hq hq1 hρ hσ
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hsig : 4 * (σ * n) ≤ ρ ^ 2 * u / 100 := by
    have := mul_le_mul_of_nonneg_right h4 hn.le
    have h2 : ρ ^ 2 * (7 * q / 8 * n) ≤ ρ ^ 2 * u := mul_le_mul_of_nonneg_left hu (by positivity)
    nlinarith
  have hbig : 400 ≤ ρ ^ 2 * u := by nlinarith
  have hKg0 : ρ ^ 2 * u / 80 ≤ Kg := by linarith
  have hKgpos : 0 < Kg := lt_of_lt_of_le (by positivity) hKg0
  -- the bracket
  have hbr : ρ ^ 2 * u / 2 ≤ 2 * M - 12 * Kg - 12 * D := by linarith
  have hmain : Kg * (ρ ^ 2 * u / 2) ≤ Kg * (2 * M - 12 * Kg - 12 * D) :=
    mul_le_mul_of_nonneg_left hbr hKgpos.le
  have hlow : ρ ^ 2 * u / 80 * (ρ ^ 2 * u / 2) ≤ Kg * (ρ ^ 2 * u / 2) :=
    mul_le_mul_of_nonneg_right hKg0 (by positivity)
  -- `3 n D` is tiny
  have hnD : n * D ≤ n * (σ * n) := mul_le_mul_of_nonneg_left hD hn.le
  have hσ' : σ * n * n * 3 < ρ ^ 2 * u / 80 * (ρ ^ 2 * u / 2) := by
    have hu2 : (7 * q / 8 * n) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ (by positivity) hu 2
    have e1 : σ * n * n * 3 = 3 * ρ ^ 4 * q ^ 2 * n ^ 2 / 10 ^ 4 := by rw [hσ]; ring
    have e2 : ρ ^ 2 * u / 80 * (ρ ^ 2 * u / 2) = ρ ^ 4 * u ^ 2 / 160 := by ring
    rw [e1, e2]
    have hr4 : 0 < ρ ^ 4 := by positivity
    have := mul_le_mul_of_nonneg_left hu2 hr4.le
    have hqn : 0 < q ^ 2 * n ^ 2 := by positivity
    nlinarith
  nlinarith

/-- Lower bound for the common apex supply. -/
lemma apex_supply_bound {q ρ σ θ n u z ε : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1 / 100) (hρ : ρ = q ^ 2 / 4000)
    (hσ : σ = ρ ^ 4 * q ^ 2 / 10 ^ 4) (hθ : θ ≤ 1 / 100) (hn : 0 ≤ n)
    (hu : 7 * q / 8 * n ≤ u) (hz : z ≤ 9 * q / 8 * u) (hε : ε ≤ σ) :
    44 / 100 * (ρ ^ 2 * u) ≤
      ρ ^ 2 * ((1 / 2 - 2 * θ) * u - 2 * z - 2 * (q / 1000 * n)) - ε * n := by
  have hr0 := rho_pos hq hρ
  have h4 := four_sig_le hq hq1 hρ hσ
  have hu0 : 0 ≤ u := le_trans (by positivity) hu
  have hsig : 4 * (σ * n) ≤ ρ ^ 2 * u / 100 := by
    have := mul_le_mul_of_nonneg_right h4 hn
    have h2 : ρ ^ 2 * (7 * q / 8 * n) ≤ ρ ^ 2 * u := mul_le_mul_of_nonneg_left hu (by positivity)
    nlinarith
  have hεn : ε * n ≤ σ * n := mul_le_mul_of_nonneg_right hε hn
  have hin : (1 / 2 - 2 * θ) * u - 2 * z - 2 * (q / 1000 * n) - 45 / 100 * u ≥ 0 := by
    have h1 : z ≤ 9 / 800 * u := by nlinarith
    have h2 : q * n ≤ 8 / 7 * u := by nlinarith
    have h3 : θ * u ≤ u / 100 := by nlinarith
    nlinarith
  have := mul_le_mul_of_nonneg_left hin (sq_nonneg ρ)
  nlinarith

/-- Logarithmic growth cutoff. -/
lemma exists_log_cutoff (c : ℝ) (hc : 0 < c) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 4 * Real.log n + 8 ≤ c * n := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ c / 8 * x := by
    have := Real.isLittleO_log_id_atTop.bound (c := c / 8) (by positivity)
    filter_upwards [this, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1),
      abs_of_nonneg (show (0 : ℝ) ≤ id x by simp only [id]; linarith)] at hx
    simpa using hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, 16 / c ≤ x := Filter.eventually_ge_atTop _
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually (h1.and h2))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨ha, hb⟩ := hN n hn
  have : 8 ≤ c / 2 * n := by
    have := mul_le_mul_of_nonneg_left hb (by positivity : (0 : ℝ) ≤ c / 2)
    rw [show c / 2 * (16 / c) = 8 by field_simp; ring] at this
    exact this
  nlinarith

end NashWilliams18.Case124.BoundedCore.RoundConst
