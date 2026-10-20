/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Stage13

/-! # Finite Bernoulli exposure and the rare-coordinate variance budget

The future average is constructed recursively on the Boolean cube. Monotonicity
and preservation of constants transfer a pointwise coordinate bound to the
two conditional future averages. The actual one-coin centered increments then
have variance `q * (1-q) * gap²`, bounded by `q * bound²`, not `bound²`.
This does not assert the full martingale exponential estimate or nibble theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BernoulliExposure

def coinMean (q : ℝ) (f : Bool → ℝ) : ℝ := (1 - q) * f false + q * f true

def coinIncrement (q : ℝ) (f : Bool → ℝ) (bit : Bool) : ℝ := f bit - coinMean q f

theorem increment_false (q : ℝ) (f : Bool → ℝ) :
    coinIncrement q f false = -q * (f true - f false) := by
  unfold coinIncrement coinMean
  ring

theorem increment_true (q : ℝ) (f : Bool → ℝ) :
    coinIncrement q f true = (1 - q) * (f true - f false) := by
  unfold coinIncrement coinMean
  ring

theorem increment_centered (q : ℝ) (f : Bool → ℝ) :
    coinMean q (coinIncrement q f) = 0 := by
  unfold coinMean
  rw [increment_false, increment_true]
  ring

theorem increment_second_moment (q : ℝ) (f : Bool → ℝ) :
    coinMean q (fun bit => coinIncrement q f bit ^ 2) =
      q * (1 - q) * (f true - f false) ^ 2 := by
  simp only [coinMean, increment_false, increment_true]
  ring

theorem increment_variance_le (q bound : ℝ) (f : Bool → ℝ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hgap : |f true - f false| ≤ bound) :
    coinMean q (fun bit => coinIncrement q f bit ^ 2) ≤ q * bound ^ 2 := by
  rw [increment_second_moment]
  have hbound : 0 ≤ bound := (abs_nonneg _).trans hgap
  have hsq : (f true - f false) ^ 2 ≤ bound ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg _) hbound).mpr hgap
    simpa only [sq_abs] using h
  have hcoeff : 0 ≤ q * (1 - q) := mul_nonneg hq0 (sub_nonneg.mpr hq1)
  calc
    q * (1 - q) * (f true - f false) ^ 2 ≤ q * (1 - q) * bound ^ 2 :=
      mul_le_mul_of_nonneg_left hsq hcoeff
    _ ≤ q * bound ^ 2 := by
      nlinarith [mul_nonneg (sq_nonneg q) (sq_nonneg bound)]

def cubeMean : {n : ℕ} → (Fin n → ℝ) → ((Fin n → Bool) → ℝ) → ℝ
  | 0, _, f => f Fin.elim0
  | n + 1, q, f => coinMean (q 0)
      (fun bit => cubeMean (fun i : Fin n => q i.succ) (fun ω => f (Fin.cons bit ω)))

theorem cubeMean_const {n : ℕ} (q : Fin n → ℝ) (a : ℝ) :
    cubeMean q (fun _ => a) = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeMean, ih, coinMean]
    ring

theorem cubeMean_mono {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f g : (Fin n → Bool) → ℝ) (hfg : ∀ ω, f ω ≤ g ω) :
    cubeMean q f ≤ cubeMean q g := by
  induction n with
  | zero => exact hfg Fin.elim0
  | succ n ih =>
    unfold cubeMean coinMean
    apply add_le_add
    · apply mul_le_mul_of_nonneg_left
      · exact ih _ (fun i => hq i.succ) _ _ (fun ω => hfg (Fin.cons false ω))
      · exact sub_nonneg.mpr (hq 0).2
    · apply mul_le_mul_of_nonneg_left
      · exact ih _ (fun i => hq i.succ) _ _ (fun ω => hfg (Fin.cons true ω))
      · exact (hq 0).1

theorem cubeMean_sub {n : ℕ} (q : Fin n → ℝ) (f g : (Fin n → Bool) → ℝ) :
    cubeMean q (fun ω => f ω - g ω) = cubeMean q f - cubeMean q g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeMean, coinMean, ih]
    ring

theorem future_gap_bound {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (f g : (Fin n → Bool) → ℝ) (bound : ℝ)
    (hgap : ∀ ω, |f ω - g ω| ≤ bound) :
    |cubeMean q f - cubeMean q g| ≤ bound := by
  rw [← cubeMean_sub, abs_le]
  constructor
  · have hb := cubeMean_mono q hq (fun _ => -bound) (fun ω => f ω - g ω)
      (fun ω => (abs_le.mp (hgap ω)).1)
    simpa only [cubeMean_const] using hb
  · have hb := cubeMean_mono q hq (fun ω => f ω - g ω) (fun _ => bound)
      (fun ω => (abs_le.mp (hgap ω)).2)
    simpa only [cubeMean_const] using hb

theorem exposure_variance_le {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (headProb bound : ℝ)
    (hp0 : 0 ≤ headProb) (hp1 : headProb ≤ 1)
    (f : Bool → (Fin n → Bool) → ℝ)
    (hgap : ∀ ω, |f true ω - f false ω| ≤ bound) :
    let conditional := fun bit => cubeMean q (f bit)
    coinMean headProb (fun bit => coinIncrement headProb conditional bit ^ 2) ≤
      headProb * bound ^ 2 := by
  exact increment_variance_le headProb bound _ hp0 hp1
    (future_gap_bound q hq _ _ bound hgap)

end PartitionedTriangleAbsorption.BernoulliExposure
