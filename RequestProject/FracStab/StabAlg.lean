/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib

/-!
# Algebraic stability of the four part value bound (towards Lemma 8.7)

Lemma 5.2 (`four_point`) says that for `x₁ + ⋯ + x₄ = 1`, `xᵢ ≥ 0`, and a triangle-thin
`[0,1]`-weighting `a`, the value `∑ aᵢⱼ xᵢ xⱼ` is at most `1/4`.  Here we record the two
explicit sum-of-squares certificates behind that bound (`sosA`, `sosB`) and read off the
stability information they contain: if the value is at least `1/4 - ρ²`, then every term of the
certificate is at most `ρ²`.
-/

namespace NashWilliams.Frac

/-- Certificate for the case `x₁ ≥ x₂ + x₃` (with `x` sorted). -/
lemma sosA (x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 : ℝ) :
    (x1+x2+x3+x4)^2/4 - (a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4)
      = (x1-x2-x3-x4)^2/4 + (1-a12)*x2*(x1-x3-x4) + (1-a13)*x3*(x1-x2-x4)
        + (1-a14)*x4*(x1-x2-x3) + (2-a12-a13-a23)*(x2*x3) + (2-a12-a14-a24)*(x2*x4)
        + (2-a13-a14-a34)*(x3*x4) := by ring

/-- Certificate for the case `x₁ ≤ x₂ + x₃` (with `x` sorted). -/
lemma sosB (x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 : ℝ) :
    (x1+x2+x3+x4)^2/4 - (a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4)
      = (x1+x4-x2-x3)^2/4 + (1-a12)*((x1-x3)*(x2-x4)) + (1-a13)*((x1-x2)*(x3-x4))
        + (2-a12-a13-a23)*(x2*x3 - x4*(x2+x3-x1)/2) + (2-a12-a14-a24)*(x4*(x1+x2-x3)/2)
        + (2-a13-a14-a34)*(x4*(x1+x3-x2)/2) + (2-a23-a24-a34)*(x4*(x2+x3-x1)/2) := by ring

/-- A small helper: `b y (y - 2ρ) ≤ ρ²` with `b ∈ [0,1]` forces `b y ≤ 4ρ`. -/
lemma small_of_quad {b y ρ : ℝ} (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hy : 0 ≤ y) (hρ : 0 ≤ ρ)
    (h : b * y * (y - 2 * ρ) ≤ ρ ^ 2) : b * y ≤ 4 * ρ := by
  rcases le_total y (4 * ρ) with hy4 | hy4
  · nlinarith
  · have h1 : y / 2 ≤ y - 2 * ρ := by linarith
    have h2 : b * y * (y / 2) ≤ ρ ^ 2 := le_trans (by
      apply mul_le_mul_of_nonneg_left h1 (mul_nonneg hb0 hy)) h
    have h3 : (b * y) ^ 2 ≤ b * y ^ 2 := by
      have : b ^ 2 ≤ b := by nlinarith
      nlinarith [sq_nonneg y]
    nlinarith [sq_nonneg (b * y), mul_nonneg hb0 hy]

/-- Common hypotheses: a triangle-thin `[0,1]`-weighting of `K₄`. -/
structure ThinK4 (a12 a13 a14 a23 a24 a34 : ℝ) : Prop where
  n12 : 0 ≤ a12
  n13 : 0 ≤ a13
  n14 : 0 ≤ a14
  n23 : 0 ≤ a23
  n24 : 0 ≤ a24
  n34 : 0 ≤ a34
  l12 : a12 ≤ 1
  l13 : a13 ≤ 1
  l14 : a14 ≤ 1
  l23 : a23 ≤ 1
  l24 : a24 ≤ 1
  l34 : a34 ≤ 1
  t123 : a12 + a13 + a23 ≤ 2
  t124 : a12 + a14 + a24 ≤ 2
  t134 : a13 + a14 + a34 ≤ 2
  t234 : a23 + a24 + a34 ≤ 2

/-- **Regime A** (`x₁ ≥ x₂ + x₃`): the first part is almost `1/2` and almost all of its pairs to
the other parts have weight close to `1` (a *star-cut*). -/
lemma regimeA {x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 ρ : ℝ}
    (hT : ThinK4 a12 a13 a14 a23 a24 a34) (h4 : 0 ≤ x4) (h34 : x4 ≤ x3) (h23 : x3 ≤ x2)
    (hsum : x1 + x2 + x3 + x4 = 1) (hA : x2 + x3 ≤ x1) (hρ : 0 ≤ ρ)
    (hval : 1/4 - ρ^2 ≤ a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4) :
    |x1 - 1/2| ≤ ρ ∧ (1 - a12) * x1 * x2 ≤ 4 * ρ ∧ (1 - a13) * x1 * x3 ≤ 4 * ρ ∧
      (1 - a14) * x1 * x4 ≤ 4 * ρ := by
  obtain ⟨n12, n13, n14, n23, n24, n34, l12, l13, l14, l23, l24, l34, t123, t124, t134, t234⟩ := hT
  have e := sosA x1 x2 x3 x4 a12 a13 a14 a23 a24 a34
  rw [hsum] at e
  have h3 : 0 ≤ x3 := by linarith
  have h2 : 0 ≤ x2 := by linarith
  have h1 : x1 ≤ 1 := by linarith
  have q1 : 0 ≤ (1-a12)*x2*(x1-x3-x4) :=
    mul_nonneg (mul_nonneg (by linarith) h2) (by linarith)
  have q2 : 0 ≤ (1-a13)*x3*(x1-x2-x4) :=
    mul_nonneg (mul_nonneg (by linarith) h3) (by linarith)
  have q3 : 0 ≤ (1-a14)*x4*(x1-x2-x3) :=
    mul_nonneg (mul_nonneg (by linarith) h4) (by linarith)
  have q4 : 0 ≤ (2-a12-a13-a23)*(x2*x3) := mul_nonneg (by linarith) (mul_nonneg h2 h3)
  have q5 : 0 ≤ (2-a12-a14-a24)*(x2*x4) := mul_nonneg (by linarith) (mul_nonneg h2 h4)
  have q6 : 0 ≤ (2-a13-a14-a34)*(x3*x4) := mul_nonneg (by linarith) (mul_nonneg h3 h4)
  have hσ : 0 ≤ (x1-x2-x3-x4)^2/4 := by positivity
  have h14 : (1:ℝ)^2/4 = 1/4 := by norm_num
  have hs0 : (x1-x2-x3-x4)^2/4 ≤ ρ^2 := by linarith
  have hs : (x1-x2-x3-x4)^2 ≤ (2*ρ)^2 := by
    have : (2*ρ)^2 = 4*ρ^2 := by ring
    rw [this]; linarith
  have hd := abs_le_of_sq_le_sq' hs (by linarith)
  have hx1 : |x1 - 1/2| ≤ ρ := abs_le.2 ⟨by linarith [hd.1], by linarith [hd.2]⟩
  have hb : ∀ {b y z : ℝ}, 0 ≤ b → b ≤ 1 → 0 ≤ y → y - 2 * ρ ≤ z → b * y * z ≤ ρ ^ 2 →
      (b) * x1 * y ≤ 4 * ρ := by
    intro b y z hb0 hb1 hy hz hbz
    have : b * y * (y - 2 * ρ) ≤ ρ ^ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hz (mul_nonneg hb0 hy)) hbz
    have := small_of_quad hb0 hb1 hy hρ this
    have hx10 : 0 ≤ x1 := by linarith
    nlinarith [mul_nonneg hb0 hy]
  have hq : (1-a12)*x2*(x1-x3-x4) + (1-a13)*x3*(x1-x2-x4) + (1-a14)*x4*(x1-x2-x3) ≤ ρ^2 := by
    linarith only [e, hval, hσ, h14, q4, q5, q6]
  refine ⟨hx1, ?_, ?_, ?_⟩
  · exact hb (z := x1-x3-x4) (by linarith) (by linarith) h2 (by linarith [hd.1])
      (by linarith only [hq, q1, q2, q3])
  · exact hb (z := x1-x2-x4) (by linarith) (by linarith) h3 (by linarith [hd.1])
      (by linarith only [hq, q1, q2, q3])
  · exact hb (z := x1-x2-x3) (by linarith) (by linarith) h4 (by linarith [hd.1])
      (by linarith only [hq, q1, q2, q3])

/-- The terms of the certificate `sosB` are nonnegative in regime B. -/
lemma regimeB_terms {x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 ρ : ℝ}
    (hT : ThinK4 a12 a13 a14 a23 a24 a34) (h4 : 0 ≤ x4) (h34 : x4 ≤ x3) (h23 : x3 ≤ x2)
    (h12 : x2 ≤ x1) (hsum : x1 + x2 + x3 + x4 = 1) (hB : x1 ≤ x2 + x3)
    (hval : 1/4 - ρ^2 ≤ a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4) :
    (x1+x4-x2-x3)^2/4 ≤ ρ^2 ∧ (1-a12)*((x1-x3)*(x2-x4)) ≤ ρ^2 ∧
      (1-a13)*((x1-x2)*(x3-x4)) ≤ ρ^2 ∧ (2-a12-a13-a23)*(x2*x3 - x4*(x2+x3-x1)/2) ≤ ρ^2 ∧
      (2-a12-a14-a24)*(x4*(x1+x2-x3)/2) ≤ ρ^2 ∧ (2-a13-a14-a34)*(x4*(x1+x3-x2)/2) ≤ ρ^2 ∧
      (2-a23-a24-a34)*(x4*(x2+x3-x1)/2) ≤ ρ^2 := by
  obtain ⟨n12, n13, n14, n23, n24, n34, l12, l13, l14, l23, l24, l34, t123, t124, t134, t234⟩ := hT
  have e := sosB x1 x2 x3 x4 a12 a13 a14 a23 a24 a34
  rw [hsum] at e
  have h3 : 0 ≤ x3 := by linarith
  have h2 : 0 ≤ x2 := by linarith
  have hσ : 0 ≤ (x1+x4-x2-x3)^2/4 := by positivity
  have h14 : (1:ℝ)^2/4 = 1/4 := by norm_num
  have q1 : 0 ≤ (1-a12)*((x1-x3)*(x2-x4)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have q2 : 0 ≤ (1-a13)*((x1-x2)*(x3-x4)) :=
    mul_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have c3 : 0 ≤ x2*x3 - x4*(x2+x3-x1)/2 := by
    have : x4*(x2+x3-x1) ≤ x3*x2 :=
      mul_le_mul h34 (by linarith) (by linarith) h3
    nlinarith [mul_nonneg h2 h3]
  have q3 : 0 ≤ (2-a12-a13-a23)*(x2*x3 - x4*(x2+x3-x1)/2) := mul_nonneg (by linarith) c3
  have q4 : 0 ≤ (2-a12-a14-a24)*(x4*(x1+x2-x3)/2) :=
    mul_nonneg (by linarith) (by have := mul_nonneg h4 (by linarith : (0:ℝ) ≤ x1+x2-x3); linarith)
  have q5 : 0 ≤ (2-a13-a14-a34)*(x4*(x1+x3-x2)/2) :=
    mul_nonneg (by linarith) (by have := mul_nonneg h4 (by linarith : (0:ℝ) ≤ x1+x3-x2); linarith)
  have q6 : 0 ≤ (2-a23-a24-a34)*(x4*(x2+x3-x1)/2) :=
    mul_nonneg (by linarith) (by have := mul_nonneg h4 (by linarith : (0:ℝ) ≤ x2+x3-x1); linarith)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    linarith only [e, hval, hσ, h14, q1, q2, q3, q4, q5, q6]

/-- **Regime B with a tiny last part** (`x₁ ≤ x₂ + x₃`, `x₄ ≤ κ`): a *cycle/star-cut* with sides
`{1,4}` and `{2,3}`. -/
lemma regimeB_small {x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 ρ κ : ℝ}
    (hT : ThinK4 a12 a13 a14 a23 a24 a34) (h4 : 0 ≤ x4) (h34 : x4 ≤ x3) (h23 : x3 ≤ x2)
    (h12 : x2 ≤ x1) (hsum : x1 + x2 + x3 + x4 = 1) (hB : x1 ≤ x2 + x3)
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1/64) (hκ1 : κ ≤ 1/64) (hx4 : x4 ≤ κ)
    (hval : 1/4 - ρ^2 ≤ a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4) :
    |x1 + x4 - 1/2| ≤ ρ ∧ (1 - a12) * x1 * x2 ≤ ρ ∧ (1 - a13) * x1 * x3 ≤ 4 * ρ + κ ∧
      (1 - a24) * x4 * x2 ≤ κ ∧ (1 - a34) * x4 * x3 ≤ κ := by
  obtain ⟨hσ, h1, h2', -, -, -, -⟩ := regimeB_terms hT h4 h34 h23 h12 hsum hB hval
  obtain ⟨n12, n13, n14, n23, n24, n34, l12, l13, l14, l23, l24, l34, -, -, -, -⟩ := hT
  have hs : (x1+x4-x2-x3)^2 ≤ (2*ρ)^2 := by
    have : (2*ρ)^2 = 4*ρ^2 := by ring
    rw [this]; linarith
  have hd := abs_le_of_sq_le_sq' hs (by linarith)
  have hx3 : 0 ≤ x3 := by linarith
  have hx2 : 0 ≤ x2 := by linarith
  have hx1 : x1 ≤ 1 := by linarith
  refine ⟨abs_le.2 ⟨by linarith [hd.1], by linarith [hd.2]⟩, ?_, ?_, ?_, ?_⟩
  · -- `x₁ - x₃ ≥ 1/8` and `x₂ - x₄ ≥ 1/8`
    have e1 : 1/8 ≤ x1 - x3 := by linarith [hd.1, hd.2]
    have e2 : 1/8 ≤ x2 - x4 := by linarith [hd.1, hd.2]
    have : (1 - a12) * (1/8 * (1/8)) ≤ ρ^2 :=
      le_trans (mul_le_mul_of_nonneg_left (mul_le_mul e1 e2 (by norm_num) (by linarith))
        (by linarith)) h1
    have hb : 1 - a12 ≤ ρ := by nlinarith
    have hx12 : x1 * x2 ≤ 1 := by nlinarith
    calc (1 - a12) * x1 * x2 = (1 - a12) * (x1 * x2) := by ring
      _ ≤ (1 - a12) * 1 := mul_le_mul_of_nonneg_left hx12 (by linarith)
      _ ≤ ρ := by linarith
  · have hy : 0 ≤ x3 - x4 := by linarith
    have key : (1 - a13) * (x3 - x4) * ((x3 - x4) - 2 * ρ) ≤ ρ ^ 2 := by
      have : (x3 - x4) - 2 * ρ ≤ x1 - x2 := by linarith [hd.1]
      calc (1 - a13) * (x3 - x4) * ((x3 - x4) - 2 * ρ) ≤ (1 - a13) * (x3 - x4) * (x1 - x2) :=
            mul_le_mul_of_nonneg_left this (mul_nonneg (by linarith) hy)
        _ = (1-a13)*((x1-x2)*(x3-x4)) := by ring
        _ ≤ ρ ^ 2 := h2'
    have hk := small_of_quad (by linarith) (by linarith) hy hρ key
    have : (1 - a13) * x3 ≤ 4 * ρ + κ := by nlinarith
    have hx10 : 0 ≤ x1 := by linarith
    have hp := mul_nonneg (by linarith only [l13] : (0:ℝ) ≤ 1 - a13) hx3
    calc (1 - a13) * x1 * x3 = x1 * ((1 - a13) * x3) := by ring
      _ ≤ 1 * ((1 - a13) * x3) := mul_le_mul_of_nonneg_right hx1 hp
      _ ≤ 4 * ρ + κ := by linarith
  · have hp1 : (1 - a24) * x2 ≤ 1 :=
      mul_le_one₀ (by linarith only [n24]) hx2 (by linarith only [hsum, h4, h34, h23, h12])
    calc (1 - a24) * x4 * x2 = x4 * ((1 - a24) * x2) := by ring
      _ ≤ x4 * 1 := mul_le_mul_of_nonneg_left hp1 h4
      _ ≤ κ := by rw [mul_one]; exact hx4
  · have hp1 : (1 - a34) * x3 ≤ 1 :=
      mul_le_one₀ (by linarith only [n34]) hx3 (by linarith only [hsum, h4, h34, h23, h12])
    calc (1 - a34) * x4 * x3 = x4 * ((1 - a34) * x3) := by ring
      _ ≤ x4 * 1 := mul_le_mul_of_nonneg_left hp1 h4
      _ ≤ κ := by rw [mul_one]; exact hx4

/-- **Regime B with all parts large** (`x₁ ≤ x₂ + x₃`, `x₄ ≥ κ`): all four triangle sums are
close to `2`. -/
lemma regimeB_big {x1 x2 x3 x4 a12 a13 a14 a23 a24 a34 ρ κ : ℝ}
    (hT : ThinK4 a12 a13 a14 a23 a24 a34) (h34 : x4 ≤ x3) (h23 : x3 ≤ x2)
    (h12 : x2 ≤ x1) (hsum : x1 + x2 + x3 + x4 = 1) (hB : x1 ≤ x2 + x3)
    (hρ : 0 ≤ ρ) (hκ : 0 < κ) (hρκ : ρ ≤ κ / 4) (hx4 : κ ≤ x4)
    (hval : 1/4 - ρ^2 ≤ a12*x1*x2 + a13*x1*x3 + a14*x1*x4 + a23*x2*x3 + a24*x2*x4 + a34*x3*x4) :
    |x1 + x4 - 1/2| ≤ ρ ∧ (2-a12-a13-a23) * κ^2 ≤ 4 * ρ^2 ∧ (2-a12-a14-a24) * κ^2 ≤ 4 * ρ^2 ∧
      (2-a13-a14-a34) * κ^2 ≤ 4 * ρ^2 ∧ (2-a23-a24-a34) * κ^2 ≤ 4 * ρ^2 := by
  have h4 : 0 ≤ x4 := by linarith
  obtain ⟨hσ, -, -, h3, h4', h5, h6⟩ := regimeB_terms hT h4 h34 h23 h12 hsum hB hval
  obtain ⟨n12, n13, n14, n23, n24, n34, l12, l13, l14, l23, l24, l34, t123, t124, t134, t234⟩ := hT
  have hs : (x1+x4-x2-x3)^2 ≤ (2*ρ)^2 := by
    have : (2*ρ)^2 = 4*ρ^2 := by ring
    rw [this]; linarith
  have hd := abs_le_of_sq_le_sq' hs (by linarith)
  have hx3 : κ ≤ x3 := by linarith
  have hx2 : κ ≤ x2 := by linarith
  have hx1 : κ ≤ x1 := by linarith
  have hk2 : 0 ≤ κ^2 := sq_nonneg κ
  refine ⟨abs_le.2 ⟨by linarith [hd.1], by linarith [hd.2]⟩, ?_, ?_, ?_, ?_⟩
  · have c : κ^2/2 ≤ x2*x3 - x4*(x2+x3-x1)/2 := by
      have h1 : x4*(x2+x3-x1) ≤ x3*x2 := mul_le_mul h34 (by linarith) (by linarith) (by linarith)
      have h2 : κ*κ ≤ x2*x3 := mul_le_mul hx2 hx3 hκ.le (by linarith)
      have e : κ^2 = κ*κ := by ring
      have e2 : x3*x2 = x2*x3 := by ring
      linarith
    have hm := mul_le_mul_of_nonneg_left c (by linarith : (0:ℝ) ≤ 2-a12-a13-a23)
    have e : (2-a12-a13-a23) * κ^2 = 2 * ((2-a12-a13-a23) * (κ^2/2)) := by ring
    have hρ2 : 0 ≤ ρ^2 := sq_nonneg ρ
    linarith only [hm, e, h3, hρ2]
  · have c : κ^2/2 ≤ x4*(x1+x2-x3)/2 := by
      have h1 : x4*x1 ≤ x4*(x1+x2-x3) := mul_le_mul_of_nonneg_left (by linarith) h4
      have h2 : κ*κ ≤ x4*x1 := mul_le_mul hx4 hx1 hκ.le h4
      have e : κ^2 = κ*κ := by ring
      linarith
    have hm := mul_le_mul_of_nonneg_left c (by linarith : (0:ℝ) ≤ 2-a12-a14-a24)
    have e : (2-a12-a14-a24) * κ^2 = 2 * ((2-a12-a14-a24) * (κ^2/2)) := by ring
    have hρ2 : 0 ≤ ρ^2 := sq_nonneg ρ
    linarith only [hm, e, h4', hρ2]
  · have c : κ^2/2 ≤ x4*(x1+x3-x2)/2 := by
      have h1 : x4*x3 ≤ x4*(x1+x3-x2) := mul_le_mul_of_nonneg_left (by linarith) h4
      have h2 : κ*κ ≤ x4*x3 := mul_le_mul hx4 hx3 hκ.le h4
      have e : κ^2 = κ*κ := by ring
      linarith
    have hm := mul_le_mul_of_nonneg_left c (by linarith : (0:ℝ) ≤ 2-a13-a14-a34)
    have e : (2-a13-a14-a34) * κ^2 = 2 * ((2-a13-a14-a34) * (κ^2/2)) := by ring
    have hρ2 : 0 ≤ ρ^2 := sq_nonneg ρ
    linarith only [hm, e, h5, hρ2]
  · have c : κ^2/4 ≤ x4*(x2+x3-x1)/2 := by
      have h0 : κ/2 ≤ x2 + x3 - x1 := by linarith [hd.2]
      have h2 : κ*(κ/2) ≤ x4*(x2+x3-x1) := mul_le_mul hx4 h0 (by linarith) h4
      have e : κ^2 = κ*κ := by ring
      linarith
    have hm := mul_le_mul_of_nonneg_left c (by linarith : (0:ℝ) ≤ 2-a23-a24-a34)
    have e : (2-a23-a24-a34) * κ^2 = 4 * ((2-a23-a24-a34) * (κ^2/4)) := by ring
    have hρ2 : 0 ≤ ρ^2 := sq_nonneg ρ
    linarith only [hm, e, h6, hρ2]

end NashWilliams.Frac
