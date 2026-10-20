/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Algebra.Order.Field.GeomSum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.NormCast
public import Lean.Elab.Tactic.Omega

/-! # Numerical estimates for the robust matching union bound

* `choose_le_pow_three` : `C(n,a) ≤ (3n/a)^a`;
* `term_one_le`, `term_two_le` : the two families of union-bound terms are at most `16^{-a}`;
* `sum_Icc_pow_le` : the geometric tail `∑_{a=1}^m 16^{-a} ≤ 1/15`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset

theorem pow_div_factorial_le_three_pow (a : ℕ) :
    (a : ℝ) ^ a / a.factorial ≤ 3 ^ a := by
  have h1 := Real.pow_div_factorial_le_exp (a : ℝ) (Nat.cast_nonneg a) a
  have h2 : Real.exp (a : ℝ) = Real.exp 1 ^ a := by
    rw [← Real.exp_nat_mul]; ring_nf
  have h3 : Real.exp 1 ^ a ≤ 3 ^ a :=
    pow_le_pow_left₀ (Real.exp_pos 1).le
      (by have := Real.exp_one_lt_d9; linarith) a
  linarith

/-- `C(n,a) ≤ (3n/a)^a` for `a ≥ 1`. -/
theorem choose_le_pow_three (n a : ℕ) (ha : 0 < a) :
    (n.choose a : ℝ) ≤ (3 * n / a) ^ a := by
  have h1 : (n.choose a : ℝ) ≤ (n : ℝ) ^ a / a.factorial := Nat.choose_le_pow_div a n
  have h2 := pow_div_factorial_le_three_pow a
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hf : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos a
  have hapow : (0 : ℝ) < (a : ℝ) ^ a := by positivity
  have h3 : (1 : ℝ) / a.factorial ≤ 3 ^ a / (a : ℝ) ^ a := by
    rw [div_le_div_iff₀ hf hapow]
    rw [div_le_iff₀ hf] at h2
    linarith
  calc (n.choose a : ℝ) ≤ (n : ℝ) ^ a / a.factorial := h1
    _ = (n : ℝ) ^ a * (1 / a.factorial) := by ring
    _ ≤ (n : ℝ) ^ a * (3 ^ a / (a : ℝ) ^ a) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = (3 * n / a) ^ a := by rw [div_pow, mul_pow]; ring

/-- First union-bound term (small plus sets). -/
theorem term_one_le (k a : ℕ) (ha : 1 ≤ a) (hak : a ≤ k) :
    ((3 * k).choose a : ℝ) * ((2 * k).choose a : ℝ) *
      ((a : ℝ) / (2 * k)) ^ (2 * a * 6) ≤ (1 / 16) ^ a := by
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hkR : (a : ℝ) ≤ k := by exact_mod_cast hak
  have hk0 : (0 : ℝ) < k := by linarith
  have c1 := choose_le_pow_three (3 * k) a (by omega)
  have c2 := choose_le_pow_three (2 * k) a (by omega)
  set x : ℝ := (a : ℝ) / (2 * k) with hx
  have hx0 : 0 < x := by positivity
  have hx1 : x ≤ 1 / 2 := by
    rw [hx, div_le_iff₀ (by positivity)]; linarith
  have e1 : (3 * ((3 * k : ℕ) : ℝ) / a) = 9 / 2 / x := by
    rw [hx]; push_cast; field_simp; ring
  have e2 : (3 * ((2 * k : ℕ) : ℝ) / a) = 3 / x := by
    rw [hx]; push_cast; field_simp
  rw [e1] at c1
  rw [e2] at c2
  have hbase : 9 / 2 / x * (3 / x) * x ^ 12 ≤ 1 / 16 := by
    have : 9 / 2 / x * (3 / x) * x ^ 12 = 27 / 2 * x ^ 10 := by
      field_simp; norm_num
    rw [this]
    have : x ^ 10 ≤ (1 / 2) ^ 10 := pow_le_pow_left₀ hx0.le hx1 10
    norm_num at this ⊢
    linarith
  calc ((3 * k).choose a : ℝ) * ((2 * k).choose a : ℝ) * x ^ (2 * a * 6)
      ≤ (9 / 2 / x) ^ a * (3 / x) ^ a * x ^ (2 * a * 6) := by
        gcongr
    _ = (9 / 2 / x * (3 / x) * x ^ 12) ^ a := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring_nf
    _ ≤ (1 / 16) ^ a := pow_le_pow_left₀ (by positivity) hbase a

/-- Second union-bound term (small minus sets). -/
theorem term_two_le (k b : ℕ) (hb : 1 ≤ b) (hbk : b ≤ 2 * k) :
    ((4 * k).choose b : ℝ) * ((3 * k).choose b : ℝ) *
      ((b : ℝ) / (3 * k)) ^ (3 * b * 6) ≤ (1 / 16) ^ b := by
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hkR : (b : ℝ) ≤ 2 * k := by exact_mod_cast hbk
  have hk0 : (0 : ℝ) < k := by linarith
  have c1 := choose_le_pow_three (4 * k) b (by omega)
  have c2 := choose_le_pow_three (3 * k) b (by omega)
  set y : ℝ := (b : ℝ) / (3 * k) with hy
  have hy0 : 0 < y := by positivity
  have hy1 : y ≤ 2 / 3 := by
    rw [hy, div_le_iff₀ (by positivity)]; linarith
  have e1 : (3 * ((4 * k : ℕ) : ℝ) / b) = 4 / y := by
    rw [hy]; push_cast; field_simp
  have e2 : (3 * ((3 * k : ℕ) : ℝ) / b) = 3 / y := by
    rw [hy]; push_cast; field_simp
  rw [e1] at c1
  rw [e2] at c2
  have hbase : 4 / y * (3 / y) * y ^ 18 ≤ 1 / 16 := by
    have : 4 / y * (3 / y) * y ^ 18 = 12 * y ^ 16 := by
      field_simp; norm_num
    rw [this]
    have : y ^ 16 ≤ (2 / 3) ^ 16 := pow_le_pow_left₀ hy0.le hy1 16
    norm_num at this ⊢
    linarith
  calc ((4 * k).choose b : ℝ) * ((3 * k).choose b : ℝ) * y ^ (3 * b * 6)
      ≤ (4 / y) ^ b * (3 / y) ^ b * y ^ (3 * b * 6) := by
        gcongr
    _ = (4 / y * (3 / y) * y ^ 18) ^ b := by
        rw [mul_pow, mul_pow, ← pow_mul]; ring_nf
    _ ≤ (1 / 16) ^ b := pow_le_pow_left₀ (by positivity) hbase b

theorem sum_Icc_pow_le (m : ℕ) : ∑ a ∈ Icc 1 m, ((1 : ℝ) / 16) ^ a ≤ 1 / 15 := by
  have h := geom_sum_Ico_le_of_lt_one (x := (1 : ℝ) / 16) (m := 1) (n := m + 1)
    (by norm_num) (by norm_num)
  have e : Icc 1 m = Ico 1 (m + 1) := by
    ext a; simp
  rw [e]
  refine h.trans (le_of_eq ?_)
  norm_num

end PartitionedTriangleAbsorption.TypedRefinerF0
