/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeFamily

/-! # A sufficient leftover scale for deterministic cover-down

This is the scalar budget, not the existence of the approximate packing or the
random reserve. The interval for `q` is satisfied by `floor(a/16)` when `a ≥ 32`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveBudget

theorem sparse_residue_budget (n a m r q : ℝ) (hn : 0 < n) (ha : 0 < a)
    (han : a ≤ n) (hm : m ≤ n * r / 2) (hr : 64 * n * r ≤ a ^ 2)
    (hql : a / 32 ≤ q) (hqu : q ≤ a / 16) :
    m / q + 2 * r + 4 * q < a := by
  have hq : 0 < q := lt_of_lt_of_le (by positivity : 0 < a / 32) hql
  have hrsmall : 64 * r ≤ a := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr han)]
  have hquot : m / q ≤ a / 4 := by
    apply (div_le_iff₀ hq).mpr
    nlinarith [mul_le_mul_of_nonneg_left hql ha.le]
  linarith

end PartitionedTriangleAbsorption.ReserveBudget
