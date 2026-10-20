/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RobustTransportMarginsStage258
public import Mathlib.Tactic.Ring

/-! Scaled margins for the actual complementary remainders of Stage258. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open RobustTransportMarginsStage258

/-- All numerical inputs of the small-deletion triangle producer follow
from the original hierarchy, with q=(1/4+e)n and d=(b+4e)n. -/
theorem scaled_remainder_margins (a e b n : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e) (hn : 0 < n)
    (hsmall : 1000000 * e ≤ a * a) (hb : a * b = 400 * e) :
    0 ≤ b ∧ 0 ≤ (1 / 4 + e) * n ∧ 0 ≤ (b + 4 * e) * n ∧
    3 * ((1 / 4 + e) * n) + (b + 4 * e) * n < n ∧
    3 * ((1 / 4 + e) * n) + (b + 4 * e) * n ≤ (3 / 4 + a) * n ∧
    (b + 4 * e) * n ≤ a * n ∧
    (1 - a) * n ^ 2 / 4 ≤ (n - 2 * ((1 / 4 + e) * n)) ^ 2 := by
  have hb0 : 0 ≤ b := by nlinarith
  obtain ⟨he32, hlow, _, hdense, _, _⟩ := transport_margins a e b ha ha1 hsmall hb
  have hdense' := mul_le_mul_of_nonneg_right hdense hn.le
  have hlow' := mul_le_mul_of_nonneg_right hlow hn.le
  have hen := mul_nonneg he hn.le
  have hcover := mul_le_mul_of_nonneg_right (show b + 4 * e ≤ a by linarith) hn.le
  refine ⟨hb0, mul_nonneg (by linarith) hn.le,
    mul_nonneg (by linarith) hn.le, ?_, ?_, hcover, ?_⟩
  · nlinarith
  · nlinarith
  · have hc : (1 - a) / 4 ≤ (1 / 2 - 2 * e) ^ 2 := by
      nlinarith [sq_nonneg e]
    calc
      (1 - a) * n ^ 2 / 4 = ((1 - a) / 4) * n ^ 2 := by ring
      _ ≤ (1 / 2 - 2 * e) ^ 2 * n ^ 2 := mul_le_mul_of_nonneg_right hc (sq_nonneg n)
      _ = (n - 2 * ((1 / 4 + e) * n)) ^ 2 := by ring

/-- Cancel the positive threshold an/100 in the double-counting estimate. -/
theorem exceptional_budget (a e b n s k : ℝ)
    (ha : 0 < a) (hn : 0 < n) (he : 0 ≤ e)
    (hb : a * b = 400 * e) (hs : s ≤ n)
    (hk : k * (a * n / 100) ≤ s * (4 * e * n)) : k ≤ b * n := by
  have ht : 0 < a * n / 100 := div_pos (mul_pos ha hn) (by norm_num)
  have hsn := mul_le_mul_of_nonneg_right hs
    (show 0 ≤ 4 * e * n from mul_nonneg (by linarith) hn.le)
  have heq : (b * n) * (a * n / 100) = n * (4 * e * n) := by
    calc
      (b * n) * (a * n / 100) = (a * b) * n ^ 2 / 100 := by ring
      _ = n * (4 * e * n) := by rw [hb]; ring
  exact le_of_mul_le_mul_right (hk.trans (hsn.trans_eq heq.symm)) ht

end PartitionedTriangleAbsorption.GoodRemaindersStage261
