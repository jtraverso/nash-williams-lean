/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Scalar blocks of the F1 incidence Gram inverse

For four equal classes, the triangle incidence Gram operator separates into
constant blocks, vertex contrasts and zero-row remainders. This file proves
the explicit inverses of the first two scalar systems. The identification
with the graph operator and its perturbation estimate are separate obligations.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1GramInverseStage230

/-- Four internal blocks and the four cross blocks of the F1 template. -/
structure Blocks where
  i0 : ℝ
  i1 : ℝ
  i2 : ℝ
  i3 : ℝ
  c02 : ℝ
  c03 : ℝ
  c12 : ℝ
  c13 : ℝ

/-- Normalized compatibility of the constant-block equations. -/
def Blocks.Balanced (x : Blocks) : Prop :=
  2 * (x.i0 + x.i1 + x.i2 + x.i3) = x.c02 + x.c03 + x.c12 + x.c13

/-- The constant-block system after division by `2t` and `t-1`. -/
def blockMap (x : Blocks) : Blocks where
  i0 := x.i0 + x.c02 + x.c03
  i1 := x.i1 + x.c12 + x.c13
  i2 := x.i2 + x.c02 + x.c12
  i3 := x.i3 + x.c03 + x.c13
  c02 := x.i0 + x.i2 + 4 * x.c02
  c03 := x.i0 + x.i3 + 4 * x.c03
  c12 := x.i1 + x.i2 + 4 * x.c12
  c13 := x.i1 + x.i3 + 4 * x.c13

noncomputable def blockInverse (x : Blocks) : Blocks :=
  let d0 := 4 * x.i0 - x.c02 - x.c03
  let d1 := 4 * x.i1 - x.c12 - x.c13
  let d2 := 4 * x.i2 - x.c02 - x.c12
  let d3 := 4 * x.i3 - x.c03 - x.c13
  let a0 := d0 / 2 - (d0 + d1) / 8
  let a1 := d1 / 2 - (d0 + d1) / 8
  let a2 := d2 / 2 + (d0 + d1) / 8
  let a3 := d3 / 2 + (d0 + d1) / 8
  ⟨a0, a1, a2, a3, (x.c02 - a0 - a2) / 4, (x.c03 - a0 - a3) / 4,
    (x.c12 - a1 - a2) / 4, (x.c13 - a1 - a3) / 4⟩

theorem blockMap_balanced (x : Blocks) : (blockMap x).Balanced := by
  dsimp [Blocks.Balanced, blockMap]
  ring

theorem blockMap_inverse (x : Blocks) (hx : x.Balanced) :
    blockMap (blockInverse x) = x := by
  cases x with
  | mk i0 i1 i2 i3 c02 c03 c12 c13 =>
    dsimp [Blocks.Balanced] at hx
    dsimp [blockMap, blockInverse]
    congr 1 <;> linarith

theorem blockMap_range (x : Blocks) :
    (∃ y, blockMap y = x) ↔ x.Balanced := by
  constructor
  · rintro ⟨y, rfl⟩
    exact blockMap_balanced y
  · intro hx
    exact ⟨blockInverse x, blockMap_inverse x hx⟩

theorem blockInverse_bound (x : Blocks) (r : ℝ) (hr : 0 ≤ r)
    (h0 : |x.i0| ≤ r / 2) (h1 : |x.i1| ≤ r / 2)
    (h2 : |x.i2| ≤ r / 2) (h3 : |x.i3| ≤ r / 2)
    (h02 : |x.c02| ≤ 2 * r) (h03 : |x.c03| ≤ 2 * r)
    (h12 : |x.c12| ≤ 2 * r) (h13 : |x.c13| ≤ 2 * r) :
    |(blockInverse x).i0| ≤ 5 * r ∧ |(blockInverse x).i1| ≤ 5 * r ∧
    |(blockInverse x).i2| ≤ 5 * r ∧ |(blockInverse x).i3| ≤ 5 * r ∧
    |(blockInverse x).c02| ≤ 3 * r ∧ |(blockInverse x).c03| ≤ 3 * r ∧
    |(blockInverse x).c12| ≤ 3 * r ∧ |(blockInverse x).c13| ≤ 3 * r := by
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  obtain ⟨h2l, h2u⟩ := abs_le.mp h2
  obtain ⟨h3l, h3u⟩ := abs_le.mp h3
  obtain ⟨h02l, h02u⟩ := abs_le.mp h02
  obtain ⟨h03l, h03u⟩ := abs_le.mp h03
  obtain ⟨h12l, h12u⟩ := abs_le.mp h12
  obtain ⟨h13l, h13u⟩ := abs_le.mp h13
  dsimp [blockInverse]
  repeat' constructor
  all_goals apply abs_le.mpr; constructor <;> linarith

/-- Internal coefficient of a vertex contrast. -/
noncomputable def starInternal (t a b c : ℝ) : ℝ :=
  ((3 * t - 4) * a - t * (b + c)) / (4 * t * (t - 1))

/-- Coefficient on one of the two opposite fine classes. -/
noncomputable def starCross (t a b c : ℝ) : ℝ :=
  (b - (t - 2) * starInternal t a b c) / (3 * t - 4)

theorem star_inverse (t a b c : ℝ) (ht : 4 ≤ t) :
    2 * t * starInternal t a b c +
        t * (starCross t a b c + starCross t a c b) = a ∧
    (t - 2) * starInternal t a b c + (3 * t - 4) * starCross t a b c = b ∧
    (t - 2) * starInternal t a b c + (3 * t - 4) * starCross t a c b = c := by
  have h0 : t ≠ 0 := by linarith
  have h1 : t - 1 ≠ 0 := by linarith
  have h3 : 3 * t - 4 ≠ 0 := by linarith
  have hA : 4 * t * (t - 1) * starInternal t a b c =
      (3 * t - 4) * a - t * (b + c) := by
    dsimp [starInternal]
    field_simp [h0, h1]
  have hB : (3 * t - 4) * starCross t a b c =
      b - (t - 2) * starInternal t a b c := by
    dsimp only [starCross]
    field_simp [h3]
  have hC : (3 * t - 4) * starCross t a c b =
      c - (t - 2) * starInternal t a b c := by
    dsimp only [starCross]
    rw [show starInternal t a c b = starInternal t a b c by
      simp only [starInternal, add_comm c b]]
    field_simp [h3]
  refine ⟨?_, by linarith, by linarith⟩
  apply (mul_left_cancel₀ h3)
  calc
    _ = 4 * t * (t - 1) * starInternal t a b c +
        t * ((3 * t - 4) * starCross t a b c) +
        t * ((3 * t - 4) * starCross t a c b) +
        2 * t * (t - 2) * starInternal t a b c := by ring
    _ = (3 * t - 4) * a := by rw [hA, hB, hC]; ring

theorem starInternal_bound (t a b c ε : ℝ) (ht : 4 ≤ t) (hε : 0 ≤ ε)
    (ha : |a| ≤ 3 * ε) (hb : |b| ≤ 2 * ε) (hc : |c| ≤ 2 * ε) :
    |starInternal t a b c| ≤ 5 * ε / t := by
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 := by linarith
  have h3 : 0 ≤ 3 * t - 4 := by linarith
  have hnum : |(3 * t - 4) * a - t * (b + c)| ≤
      (3 * t - 4) * (3 * ε) + t * (4 * ε) := by
    calc
      _ ≤ |(3 * t - 4) * a| + |t * (b + c)| := abs_sub _ _
      _ = (3 * t - 4) * |a| + t * |b + c| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h3, abs_of_pos ht0]
      _ ≤ (3 * t - 4) * (3 * ε) + t * (4 * ε) := by
        have hbc : |b + c| ≤ 4 * ε := (abs_add_le b c).trans (by linarith)
        exact add_le_add (mul_le_mul_of_nonneg_left ha h3)
          (mul_le_mul_of_nonneg_left hbc (le_of_lt ht0))
  rw [starInternal, abs_div, abs_of_pos (mul_pos (mul_pos (by norm_num) ht0) ht1)]
  apply (div_le_iff₀ (mul_pos (mul_pos (by norm_num) ht0) ht1)).mpr
  have heq : 5 * ε / t * (4 * t * (t - 1)) = 20 * ε * (t - 1) := by
    field_simp
    ring
  rw [heq]
  have hp := mul_nonneg hε (show 0 ≤ 7 * t - 8 by linarith)
  nlinarith

theorem starCross_bound (t a b c ε : ℝ) (ht : 4 ≤ t) (hε : 0 ≤ ε)
    (ha : |a| ≤ 3 * ε) (hb : |b| ≤ 2 * ε) (hc : |c| ≤ 2 * ε) :
    |starCross t a b c| ≤ 4 * ε / t := by
  have ht0 : 0 < t := by linarith
  have h2 : 0 ≤ t - 2 := by linarith
  have h3 : 0 < 3 * t - 4 := by linarith
  have hA := starInternal_bound t a b c ε ht hε ha hb hc
  have hnum : |b - (t - 2) * starInternal t a b c| ≤
      2 * ε + (t - 2) * (5 * ε / t) := by
    calc
      _ ≤ |b| + |(t - 2) * starInternal t a b c| := abs_sub _ _
      _ = |b| + (t - 2) * |starInternal t a b c| := by
        rw [abs_mul, abs_of_nonneg h2]
      _ ≤ _ := add_le_add hb (mul_le_mul_of_nonneg_left hA h2)
  rw [starCross, abs_div, abs_of_pos h3]
  apply (div_le_iff₀ h3).mpr
  apply hnum.trans
  apply (mul_le_mul_iff_right₀ ht0).mp
  have heq1 : (2 * ε + (t - 2) * (5 * ε / t)) * t =
      2 * ε * t + (t - 2) * (5 * ε) := by field_simp
  have heq2 : (4 * ε / t * (3 * t - 4)) * t =
      4 * ε * (3 * t - 4) := by field_simp
  rw [mul_comm t _, mul_comm t _, heq1, heq2]
  have hp := mul_nonneg hε (show 0 ≤ 5 * t - 6 by linarith)
  nlinarith

end PartitionedTriangleAbsorption.F1GramInverseStage230
