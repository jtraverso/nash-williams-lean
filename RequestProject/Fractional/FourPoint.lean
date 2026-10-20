/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Lemma 5.2 of Delcourt–Postle: the four part value bound

For nonnegative reals `x1, …, x4` and weights `aij ∈ [0,1]` such that every triangle has total
weight at most `2`, we have `∑ aij xi xj ≤ (x1 + x2 + x3 + x4)^2 / 4`.
The proof is by an explicit linear programming duality certificate, first for sorted `x`.
-/

namespace NashWilliams.Frac

lemma four_sorted (x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 : ℝ)
    (h4 : 0 ≤ x4) (h34 : x4 ≤ x3) (h23 : x3 ≤ x2) (h12 : x2 ≤ x1)
    (c12 : a12 ≤ 1) (c13 : a13 ≤ 1) (c14 : a14 ≤ 1)
    (t123 : a12 + a13 + a23 ≤ 2) (t124 : a12 + a14 + a24 ≤ 2) (t134 : a13 + a14 + a34 ≤ 2)
    (t234 : a23 + a24 + a34 ≤ 2) :
    a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4 ≤
      (x1+x2+x3+x4)^2/4 := by
  have h3 : 0 ≤ x3 := by linarith
  have h2 : 0 ≤ x2 := by linarith
  rcases le_total (x2 + x3) x1 with hA | hB
  · nlinarith [mul_nonneg (sub_nonneg.2 c12) (mul_nonneg h2 (by linarith : (0:ℝ) ≤ x1 - x3 - x4)),
      mul_nonneg (sub_nonneg.2 c13) (mul_nonneg h3 (by linarith : (0:ℝ) ≤ x1 - x2 - x4)),
      mul_nonneg (sub_nonneg.2 c14) (mul_nonneg h4 (by linarith : (0:ℝ) ≤ x1 - x2 - x3)),
      mul_nonneg (sub_nonneg.2 t123) (mul_nonneg h2 h3),
      mul_nonneg (sub_nonneg.2 t124) (mul_nonneg h2 h4),
      mul_nonneg (sub_nonneg.2 t134) (mul_nonneg h3 h4), sq_nonneg (x1 - x2 - x3 - x4)]
  · have ht : 0 ≤ x4 * (x2 + x3 - x1) / 2 := by
      have := mul_nonneg h4 (by linarith : (0:ℝ) ≤ x2 + x3 - x1); linarith
    have hz123 : 0 ≤ x2 * x3 - x4 * (x2 + x3 - x1) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h34 h2]
    nlinarith [mul_nonneg (sub_nonneg.2 c12)
        (mul_nonneg (by linarith : (0:ℝ) ≤ x1 - x3) (by linarith : (0:ℝ) ≤ x2 - x4)),
      mul_nonneg (sub_nonneg.2 c13)
        (mul_nonneg (by linarith : (0:ℝ) ≤ x1 - x2) (by linarith : (0:ℝ) ≤ x3 - x4)),
      mul_nonneg (sub_nonneg.2 t123) hz123,
      mul_nonneg (sub_nonneg.2 t124) (mul_nonneg h4 (by linarith : (0:ℝ) ≤ x1 + x2 - x3)),
      mul_nonneg (sub_nonneg.2 t134) (mul_nonneg h4 (by linarith : (0:ℝ) ≤ x1 + x3 - x2)),
      mul_nonneg (sub_nonneg.2 t234) ht, sq_nonneg (x1 + x4 - x2 - x3)]

set_option maxHeartbeats 8000000 in
/-- **Lemma 5.2** (four parts). -/
lemma four_point (x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 : ℝ)
    (h1 : 0 ≤ x1) (h2 : 0 ≤ x2) (h3 : 0 ≤ x3) (h4 : 0 ≤ x4)
    (c12 : a12 ≤ 1) (c13 : a13 ≤ 1) (c14 : a14 ≤ 1) (c23 : a23 ≤ 1) (c24 : a24 ≤ 1)
    (c34 : a34 ≤ 1)
    (t123 : a12 + a13 + a23 ≤ 2) (t124 : a12 + a14 + a24 ≤ 2) (t134 : a13 + a14 + a34 ≤ 2)
    (t234 : a23 + a24 + a34 ≤ 2) :
    a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4 ≤
      (x1+x2+x3+x4)^2/4 := by
  rcases le_total x1 x2 with _ | _ <;> rcases le_total x1 x3 with _ | _ <;>
  rcases le_total x1 x4 with _ | _ <;> rcases le_total x2 x3 with _ | _ <;>
  rcases le_total x2 x4 with _ | _ <;> rcases le_total x3 x4 with _ | _ <;>
    first
    | linarith [four_sorted x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x1 x2 x4 x3 a12 a14 a13 a24 a23 a34 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x1 x3 x2 x4 a13 a12 a14 a23 a34 a24 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x1 x3 x4 x2 a13 a14 a12 a34 a23 a24 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x1 x4 x2 x3 a14 a12 a13 a24 a34 a23 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x1 x4 x3 x2 a14 a13 a12 a34 a24 a23 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x2 x1 x3 x4 a12 a23 a24 a13 a14 a34 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x2 x1 x4 x3 a12 a24 a23 a14 a13 a34 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x2 x3 x1 x4 a23 a12 a24 a13 a34 a14 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x2 x3 x4 x1 a23 a24 a12 a34 a13 a14 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x2 x4 x1 x3 a24 a12 a23 a14 a34 a13 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x2 x4 x3 x1 a24 a23 a12 a34 a14 a13 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x3 x1 x2 x4 a13 a23 a34 a12 a14 a24 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x3 x1 x4 x2 a13 a34 a23 a14 a12 a24 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x3 x2 x1 x4 a23 a13 a34 a12 a24 a14 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x3 x2 x4 x1 a23 a34 a13 a24 a12 a14 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x3 x4 x1 x2 a34 a13 a23 a14 a24 a12 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x3 x4 x2 x1 a34 a23 a13 a24 a14 a12 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x4 x1 x2 x3 a14 a24 a34 a12 a13 a23 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x4 x1 x3 x2 a14 a34 a24 a13 a12 a23 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x4 x2 x1 x3 a24 a14 a34 a12 a23 a13 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x4 x2 x3 x1 a24 a34 a14 a23 a12 a13 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x4 x3 x1 x2 a34 a14 a24 a13 a23 a12 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]
    | linarith [four_sorted x4 x3 x2 x1 a34 a24 a14 a23 a13 a12 (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)]

end NashWilliams.Frac
