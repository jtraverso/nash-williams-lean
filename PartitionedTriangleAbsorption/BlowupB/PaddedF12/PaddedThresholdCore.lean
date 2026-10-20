/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedParameters
import PartitionedTriangleAbsorption.BlowupB.PaddedQuantitative.UniformThreshold
import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer

/-! # A single explicit order threshold, chosen before the density -/

namespace PaddedF12.PaddedThresholds

open KeevashQuantitative PaddedInputs

noncomputable def constantC : ℝ := (2 : ℝ) ^ (2 ^ 23 : ℕ)

def exponentD : ℕ := 2 ^ 20

noncomputable def orderThreshold : ℕ := uniformThreshold constantC

theorem constantC_pos : 0 < constantC := pow_pos (by norm_num) _

theorem delta_exponent_budget (m : ℕ) : δKT 4 m * (exponentD : ℝ) ≤ 1 / 2 := by
  have hq : (1 : ℝ) ≤ qT 4 m := by exact_mod_cast (show 1 ≤ qT 4 m from by
    have := qT_four_ge m
    omega)
  have hp : (1 : ℝ) ≤ (qT 4 m : ℝ) ^ 5 := one_le_pow₀ hq
  have hδ : δKT 4 m ≤ (2 : ℝ) ^ (-(21 : ℝ)) := by
    unfold δKT
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  calc
    _ ≤ (2 : ℝ) ^ (-(21 : ℝ)) * (exponentD : ℝ) :=
      mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg _)
    _ = 1 / 2 := by norm_num [exponentD, Real.rpow_neg, Real.rpow_natCast]

theorem uniform_order_budget (m n : ℕ) (hn : orderThreshold < n)
    (ω : ℝ) (hω : (n : ℝ) ^ (-δKT 4 m) < ω) :
    constantC / ω ^ exponentD < n :=
  uniform_polynomial_threshold constantC (δKT 4 m) exponentD constantC_pos.le
    (delta_exponent_budget m) n hn.le ω hω

theorem monomial_le_budget (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (a d : ℕ) (ha : a ≤ 2 ^ 23) (hd : d ≤ exponentD) :
    (2 : ℝ) ^ a / ω ^ d ≤ constantC / ω ^ exponentD := by
  apply div_le_div₀ constantC_pos.le
  · exact pow_le_pow_right₀ (by norm_num) ha
  · exact pow_pos hω _
  · exact pow_le_pow_of_le_one hω.le hω1 hd

theorem monomial_order (m n : ℕ) (hn : orderThreshold < n)
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hdensity : (n : ℝ) ^ (-δKT 4 m) < ω)
    (a d : ℕ) (ha : a ≤ 2 ^ 23) (hd : d ≤ exponentD) :
    (2 : ℝ) ^ a / ω ^ d < n :=
  (monomial_le_budget ω hω hω1 a d ha hd).trans_lt
    (uniform_order_budget m n hn ω hdensity)

/-- Algebraic normalization without evaluating the large powers of two. -/
theorem monomial_normalization (ω : ℝ) (hω : 0 < ω)
    (a b k d e l : ℕ) :
    (2 : ℝ) ^ a * ((2 : ℝ) ^ b / ω) ^ k / (ω ^ d / (2 : ℝ) ^ e) ^ l =
      (2 : ℝ) ^ (a + b * k + e * l) / ω ^ (k + d * l) := by
  simp only [pow_add, pow_mul, div_pow]
  field_simp

theorem reciprocal_normalization (ω : ℝ) (hω : 0 < ω)
    (a b c d e : ℕ) :
    (2 : ℝ) ^ a * (ω ^ b / (2 : ℝ) ^ c)⁻¹ ^ d * ω⁻¹ ^ e =
      (2 : ℝ) ^ (a + c * d) / ω ^ (b * d + e) := by
  simp only [pow_add, pow_mul, inv_div, div_pow, inv_pow]
  field_simp

#print axioms delta_exponent_budget
#print axioms uniform_order_budget
#print axioms monomial_normalization

end PaddedF12.PaddedThresholds
