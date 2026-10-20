/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# A threshold chosen before the variable density

If a construction needs `n > C / ω^D`, the hypothesis `n^(-δ) < ω`
does not permit substituting a qualitative threshold that depends on `ω`.
This file gives the quantified arithmetic bridge when `δ * D ≤ 1/2`.
The threshold is the explicit integer `ceil(C^2) + 1`, fixed before `ω`.
-/

namespace KeevashQuantitative

theorem density_power_lower (n ω δ : ℝ) (D : ℕ) (hn : 1 ≤ n)
    (hδD : δ * D ≤ 1 / 2) (hω : n ^ (-δ) < ω) :
    n ^ (-(1 / 2 : ℝ)) ≤ ω ^ D := by
  have hn0 : 0 < n := by linarith
  have hp : n ^ (-(δ * D)) ≤ ω ^ D := by
    rw [show -(δ * (D : ℝ)) = (-δ) * D by ring,
      Real.rpow_mul_natCast hn0.le]
    exact pow_le_pow_left₀ (Real.rpow_pos_of_pos hn0 _).le hω.le D
  apply le_trans ?_ hp
  exact Real.rpow_le_rpow_of_exponent_le hn (by linarith)

theorem polynomial_density_budget (C n ω δ : ℝ) (D : ℕ)
    (hC : 0 ≤ C) (hn : 1 ≤ n) (hsize : C ^ 2 < n)
    (hδD : δ * D ≤ 1 / 2) (hω : n ^ (-δ) < ω) :
    C / ω ^ D < n := by
  have hn0 : 0 < n := by linarith
  have hω0 : 0 < ω := (Real.rpow_pos_of_pos hn0 _).trans hω
  have hp := density_power_lower n ω δ D hn hδD hω
  have hm : Real.sqrt n ≤ n * ω ^ D := by
    have hmul := mul_le_mul_of_nonneg_left hp hn0.le
    calc
      Real.sqrt n = n * n ^ (-(1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow]
        convert Real.rpow_add hn0 1 (-(1 / 2 : ℝ)) using 1 <;> norm_num
      _ ≤ _ := hmul
  apply (div_lt_iff₀ (pow_pos hω0 D)).mpr
  exact ((Real.lt_sqrt hC).mpr hsize).trans_le hm

noncomputable def uniformThreshold (C : ℝ) : ℕ := ⌈C ^ 2⌉₊ + 1

/-- The size threshold is quantified before the variable density `ω`. -/
theorem uniform_polynomial_threshold (C δ : ℝ) (D : ℕ)
    (hC : 0 ≤ C) (hδD : δ * D ≤ 1 / 2) :
    ∀ n : ℕ, uniformThreshold C ≤ n →
      ∀ ω : ℝ, (n : ℝ) ^ (-δ) < ω → C / ω ^ D < n := by
  intro n hn ω hω
  have hn1 : 1 ≤ n := by unfold uniformThreshold at hn; omega
  have hsize : C ^ 2 < n := by
    have hceil := Nat.le_ceil (C ^ 2)
    have hlt : (⌈C ^ 2⌉₊ : ℝ) < n := by
      exact_mod_cast (show ⌈C ^ 2⌉₊ < n by unfold uniformThreshold at hn; omega)
    exact hceil.trans_lt hlt
  exact polynomial_density_budget C n ω δ D hC (by exact_mod_cast hn1)
    hsize hδD hω

/-- One threshold also handles a finite collection of smaller monomials. -/
theorem uniform_smaller_budget (C C' n ω δ : ℝ) (D D' : ℕ)
    (hC : 0 ≤ C) (hCC : C' ≤ C) (hDD : D' ≤ D)
    (hn : 1 ≤ n) (hsize : C ^ 2 < n) (hδD : δ * D ≤ 1 / 2)
    (hω : n ^ (-δ) < ω) (hω1 : ω ≤ 1) :
    C' / ω ^ D' < n := by
  have hn0 : 0 < n := by linarith
  have hω0 : 0 < ω := (Real.rpow_pos_of_pos hn0 _).trans hω
  apply lt_of_le_of_lt ?_ (polynomial_density_budget C n ω δ D hC hn hsize hδD hω)
  exact div_le_div₀ hC hCC (pow_pos hω0 D)
    (pow_le_pow_of_le_one hω0.le hω1 hDD)

#print axioms density_power_lower
#print axioms polynomial_density_budget
#print axioms uniform_polynomial_threshold
#print axioms uniform_smaller_budget

end KeevashQuantitative
