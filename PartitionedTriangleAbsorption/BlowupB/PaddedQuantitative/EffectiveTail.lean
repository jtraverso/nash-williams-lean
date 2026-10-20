/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# An explicit polynomial threshold for exponential tail estimates

This auxiliary is independent of the user's original project. It supplies
the quantitative replacement for the qualitative tail limit used in
`Nibble.Asymptotic.exists_pow_mul_exp_lt`; it does not assert an absorber or
any decomposition theorem.

The proof uses the term of degree `d + 1` in the exponential series. In
particular the threshold depends polynomially on `1 / c`, and all constants
are fixed before the integer `k` to which the estimate is applied.
-/

namespace KeevashQuantitative

/-- A single Taylor term gives an explicit tail estimate of arbitrary degree. -/
theorem polynomial_exp_tail_lt_one (c C x : ℝ) (d : ℕ)
    (hc : 0 < c) (_hC : 0 < C) (hx : 0 < x)
    (hlarge : C * ((d + 1).factorial : ℝ) < c ^ (d + 1) * x) :
    C * x ^ d * Real.exp (-(c * x)) < 1 := by
  have hfac : 0 < ((d + 1).factorial : ℝ) := by positivity
  have hterm := Real.pow_div_factorial_le_exp (c * x) (mul_nonneg hc.le hx.le) (d + 1)
  have hpoly : C * x ^ d < (c * x) ^ (d + 1) / ((d + 1).factorial : ℝ) := by
    rw [lt_div_iff₀ hfac, mul_pow, pow_succ x]
    have h := mul_lt_mul_of_pos_right hlarge (pow_pos hx d)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hbound := mul_lt_mul_of_pos_right (hpoly.trans_le hterm)
    (Real.exp_pos (-(c * x)))
  simpa only [← Real.exp_add, add_neg_cancel, Real.exp_zero] using hbound

/-- Explicit integer threshold. For fixed degree `d`, its real expression
before rounding has degree `d + 1` in `c⁻¹`. -/
noncomputable def tailThreshold (c C : ℝ) (d : ℕ) : ℕ :=
  ⌈C * ((d + 1).factorial : ℝ) / c ^ (d + 1)⌉₊ + 1

theorem tailThreshold_pos (c C : ℝ) (d : ℕ) : 0 < tailThreshold c C d := by
  unfold tailThreshold
  omega

/-- Every integer beyond the displayed threshold satisfies the tail bound. -/
theorem polynomial_exp_tail_of_threshold (c C : ℝ) (d : ℕ)
    (hc : 0 < c) (hC : 0 < C) (k : ℕ) (hk : tailThreshold c C d ≤ k) :
    C * (k : ℝ) ^ d * Real.exp (-(c * k)) < 1 := by
  have hkpos : 0 < k := lt_of_lt_of_le (tailThreshold_pos c C d) hk
  have hkposR : (0 : ℝ) < k := by exact_mod_cast hkpos
  apply polynomial_exp_tail_lt_one c C (k : ℝ) d hc hC hkposR
  have hceil : C * ((d + 1).factorial : ℝ) / c ^ (d + 1) ≤
      (⌈C * ((d + 1).factorial : ℝ) / c ^ (d + 1)⌉₊ : ℝ) := Nat.le_ceil _
  have hround : (⌈C * ((d + 1).factorial : ℝ) / c ^ (d + 1)⌉₊ : ℝ) < k := by
    have hnat : ⌈C * ((d + 1).factorial : ℝ) / c ^ (d + 1)⌉₊ < k := by
      unfold tailThreshold at hk
      omega
    exact_mod_cast hnat
  have hratio := hceil.trans_lt hround
  have h := (div_lt_iff₀ (pow_pos hc (d + 1))).mp hratio
  simpa only [mul_comm] using h

/-- The concrete exponent and coefficient in the existing nibble tail bound. -/
theorem nibble_tail_explicit (c : ℝ) (hc : 0 < c) (k : ℕ)
    (hk : tailThreshold c 2560 8 ≤ k) :
    2560 * (k : ℝ) ^ 8 * Real.exp (-(c * k)) < 1 :=
  polynomial_exp_tail_of_threshold c 2560 8 hc (by norm_num) k hk

theorem nibble_tailThreshold_eq (c : ℝ) :
    tailThreshold c 2560 8 = ⌈928972800 / c ^ 9⌉₊ + 1 := by
  norm_num [tailThreshold]

/-- The truncation level in the existing nibble is the iterated integer square
root. A fourth power of the explicit threshold therefore suffices. -/
theorem nibble_tail_quarter_root (c : ℝ) (hc : 0 < c) (n : ℕ)
    (hn : (tailThreshold c 2560 8) ^ 4 ≤ n) :
    2560 * (Nat.sqrt (Nat.sqrt n) : ℝ) ^ 8 *
      Real.exp (-(c * Nat.sqrt (Nat.sqrt n))) < 1 := by
  apply nibble_tail_explicit c hc
  have hsq : tailThreshold c 2560 8 * tailThreshold c 2560 8 ≤ Nat.sqrt n :=
    Nat.le_sqrt.mpr (by nlinarith only [hn])
  exact Nat.le_sqrt.mpr hsq

#print axioms polynomial_exp_tail_lt_one
#print axioms tailThreshold_pos
#print axioms polynomial_exp_tail_of_threshold
#print axioms nibble_tail_explicit
#print axioms nibble_tailThreshold_eq
#print axioms nibble_tail_quarter_root

end KeevashQuantitative
