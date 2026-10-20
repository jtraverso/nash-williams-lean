/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Explicit budgets for three independent bipartite correction sets

The larger constant accounts for adding three sets, each with its own degree
quota. The bound is sufficient, not an optimized estimate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.NeutralQuotaBudgetStage76

theorem quota_capacity (gamma r n M L R q b : ℝ)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hr : 0 < r) (hn : 0 < n)
    (hsmall : 1024 * r ≤ gamma ^ 2)
    (hM : M ≤ 4 * r * n ^ 2) (hL : gamma * n ≤ L) (hR : gamma * n ≤ R)
    (hq : 64 * r * n / gamma ≤ q) (hq1 : q ≤ 65 * r * n / gamma)
    (hb : b ≤ 3 * r * n) :
    2 * M < q * L ∧ 2 * M + 2 * q * (b + q) < q * R ∧
      r * n + 3 * q ≤ 196 * r * n / gamma := by
  have hqpos : 0 < q := (by positivity : 0 < 64 * r * n / gamma).trans_le hq
  have hqg : 64 * r * n ≤ q * gamma := (div_le_iff₀ hg).mp hq
  have hqgn := mul_le_mul_of_nonneg_right hqg hn.le
  have hm : 2 * M ≤ q * (gamma * n / 8) := by nlinarith
  have hrn : r * n ≤ r * n / gamma := by
    apply (le_div_iff₀ hg).mpr
    nlinarith [mul_le_mul_of_nonneg_left hg1 (mul_pos hr hn).le]
  have hloss : 2 * (b + q) ≤ 136 * r * n / gamma := by
    have hh : 3 * r * n ≤ 3 * (r * n / gamma) := by linarith
    have he : 3 * (r * n / gamma) = 3 * r * n / gamma := by ring
    rw [he] at hh
    calc
      2 * (b + q) ≤ 2 * (3 * r * n / gamma + 65 * r * n / gamma) := by linarith
      _ = 136 * r * n / gamma := by ring
  have hscale : 136 * r * n / gamma ≤ 17 / 128 * (gamma * n) := by
    apply (div_le_iff₀ hg).mpr
    have hh := mul_le_mul_of_nonneg_right hsmall hn.le
    nlinarith
  have hgap : q * (gamma * n / 8 + 17 / 128 * (gamma * n)) < q * (gamma * n) := by
    apply mul_lt_mul_of_pos_left _ hqpos
    nlinarith [mul_pos hg hn]
  refine ⟨?_, ?_, ?_⟩
  · exact hm.trans_lt (by
      apply lt_of_lt_of_le _ (mul_le_mul_of_nonneg_left hL hqpos.le)
      apply mul_lt_mul_of_pos_left _ hqpos
      nlinarith [mul_pos hg hn])
  · calc
      2 * M + 2 * q * (b + q) ≤
          q * (gamma * n / 8) + q * (17 / 128 * (gamma * n)) := by
        have hh := mul_le_mul_of_nonneg_left (hloss.trans hscale) hqpos.le
        nlinarith
      _ = q * (gamma * n / 8 + 17 / 128 * (gamma * n)) := by ring
      _ < q * (gamma * n) := hgap
      _ ≤ q * R := mul_le_mul_of_nonneg_left hR hqpos.le
  · calc
      r * n + 3 * q ≤ r * n / gamma + 3 * (65 * r * n / gamma) := by linarith
      _ = 196 * r * n / gamma := by ring

theorem rounded_quotas (gamma r n : ℝ) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hr : 0 < r) (hn : 0 < n) (hlarge : 1 ≤ r * n) :
    64 * r * n / gamma ≤ (⌈64 * r * n / gamma⌉₊ : ℝ) ∧
      (⌈64 * r * n / gamma⌉₊ : ℝ) ≤ 65 * r * n / gamma ∧
      2 * r * n ≤ (⌈2 * r * n⌉₊ : ℝ) ∧
      (⌈2 * r * n⌉₊ : ℝ) ≤ 3 * r * n := by
  have hunit : 1 ≤ r * n / gamma := by
    apply (le_div_iff₀ hg).mpr
    linarith
  have hq := Nat.ceil_lt_add_one (show 0 ≤ 64 * r * n / gamma by positivity)
  have hb := Nat.ceil_lt_add_one (show 0 ≤ 2 * r * n by positivity)
  refine ⟨Nat.le_ceil _, ?_, Nat.le_ceil _, ?_⟩
  · have he : 65 * r * n / gamma = 64 * r * n / gamma + r * n / gamma := by ring
    rw [he]
    linarith
  · linarith

end PartitionedTriangleAbsorption.NeutralQuotaBudgetStage76
