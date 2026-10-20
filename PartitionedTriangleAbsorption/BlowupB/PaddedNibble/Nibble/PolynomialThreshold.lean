/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.EffectiveConsumer

@[expose] public section

/-!
# A polynomial bound for the explicit nibble threshold

The threshold is bounded before choosing the density. This is the quantitative
step needed when the input permits a density that tends to zero with the order
of the graph. No compactness or density-dependent hidden threshold is used.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open KeevashQuantitative

noncomputable def packingPolynomial (b η : ℝ) : ℝ :=
  2 ^ 6500 * (b + 1) ^ 40 / η ^ 4000

theorem monomial_le_half_packingPolynomial (b η : ℝ) (hb : 0 ≤ b)
    (hη : 0 < η) (hη1 : η ≤ 1) (d j k : ℕ)
    (hd : d ≤ 6499) (hj : j ≤ 40) (hk : k ≤ 4000) :
    2 ^ d * (b + 1) ^ j / η ^ k ≤ packingPolynomial b η / 2 := by
  have hd' : (2 : ℝ) ^ d ≤ 2 ^ 6499 := pow_le_pow_right₀ (by norm_num) hd
  have hj' : (b + 1) ^ j ≤ (b + 1) ^ 40 := pow_le_pow_right₀ (by linarith) hj
  have hk' : η ^ 4000 ≤ η ^ k := pow_le_pow_of_le_one hη.le hη1 hk
  calc
    _ ≤ 2 ^ 6499 * (b + 1) ^ 40 / η ^ 4000 :=
      div_le_div₀ (by positivity)
        (mul_le_mul hd' hj' (by positivity) (by positivity)) (by positivity) hk'
    _ = _ := by
      unfold packingPolynomial
      rw [show (2 : ℝ) ^ 6500 = 2 ^ 6499 * 2 from pow_succ 2 6499]
      generalize (2 : ℝ) ^ 6499 = x
      generalize (b + 1) ^ 40 = y
      generalize η ^ 4000 = z
      ring

theorem packingPolynomial_two_le (b η : ℝ) (hb : 0 ≤ b)
    (hη : 0 < η) (hη1 : η ≤ 1) : 2 ≤ packingPolynomial b η := by
  have h := monomial_le_half_packingPolynomial b η hb hη hη1 0 0 0
    (by omega) (by omega) (by omega)
  norm_num only [pow_zero, one_mul, div_one] at h
  linarith

theorem tailThreshold_real_le (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) :
    (tailThreshold c 2560 8 : ℝ) ≤ 2 ^ 31 / c ^ 9 := by
  rw [nibble_tailThreshold_eq, Nat.cast_add, Nat.cast_one]
  have hceil := (Nat.ceil_lt_add_one (show 0 ≤ (928972800 : ℝ) / c ^ 9 by positivity)).le
  have hp : c ^ 9 ≤ 1 := pow_le_one₀ hc.le hc1
  have hstep : (928972800 : ℝ) / c ^ 9 + 2 ≤ 2 ^ 31 / c ^ 9 := by
    rw [le_div_iff₀ (pow_pos hc 9), add_mul,
      div_mul_cancel₀ _ (pow_pos hc 9).ne']
    norm_num
    nlinarith
  linarith

theorem tailFourth_le_half_packingPolynomial (b η : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    ((tailThreshold (commonRate b η) 2560 8 : ℕ) : ℝ) ^ 4 ≤
      packingPolynomial b η / 2 := by
  have hc := commonRate_pos b η hb.le hη
  have hc1 : commonRate b η ≤ 1 := by
    have h := commonRate_le_unweighted b η hb.le hη hη1 0 0 (by omega) (by omega)
    simpa using h
  have ht := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ tailThreshold (commonRate b η) 2560 8)
    (tailThreshold_real_le (commonRate b η) hc hc1) 4
  have he : (2 ^ 31 / commonRate b η ^ 9) ^ 4 =
      2 ^ 5884 * (b + 1) ^ 36 / η ^ 3672 := by
    unfold commonRate
    field_simp
  rw [he] at ht
  calc
    _ ≤ 2 ^ 5884 * (b + 1) ^ 36 / η ^ 3672 := ht
    _ ≤ packingPolynomial b η / 2 :=
      monomial_le_half_packingPolynomial b η hb.le hη hη1 5884 36 3672
        (by omega) (by omega) (by omega)

theorem rounding_below_packingPolynomial (b η x : ℝ) (hb : 0 ≤ b)
    (hη : 0 < η) (hη1 : η ≤ 1) (hx : 0 ≤ x)
    (hbound : x ≤ packingPolynomial b η / 2) :
    (⌈x⌉₊ : ℝ) ≤ packingPolynomial b η := by
  have hceil := (Nat.ceil_lt_add_one hx).le
  have htwo := packingPolynomial_two_le b η hb hη hη1
  linarith

theorem roundWeight_le_half_packingPolynomial (b η : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    4 * scheduleGamma η * scheduledWeightCap b η ≤ packingPolynomial b η / 2 := by
  have hγ : scheduleGamma η ≤ 1 := (scheduleGamma_le η hη hη1).trans (by norm_num)
  have hB := scheduledWeightCap_pos b η hb
  have hcap := scheduledWeightCap_polynomial b η hb.le hη hη1
  calc
    _ ≤ 4 * scheduledWeightCap b η := by nlinarith
    _ ≤ 2 ^ 19 * (b + 1) / η ^ 16 := by
      have h := mul_le_mul_of_nonneg_left hcap (by norm_num : (0 : ℝ) ≤ 4)
      convert h using 1; ring
    _ ≤ packingPolynomial b η / 2 := by
      simpa only [pow_one] using
        monomial_le_half_packingPolynomial b η hb.le hη hη1 19 1 16
          (by omega) (by omega) (by omega)

theorem iterationWeight_le_half_packingPolynomial (b η : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    10 * scheduleGamma η * scheduledWeightCap b η / loadTolerance η ≤
      packingPolynomial b η / 2 := by
  have hγ0 := scheduleGamma_pos η hη
  have hγ : scheduleGamma η ≤ 1 := (scheduleGamma_le η hη hη1).trans (by norm_num)
  have hB := scheduledWeightCap_pos b η hb
  have hcap := scheduledWeightCap_polynomial b η hb.le hη hη1
  have htol := loadTolerance_pos η hη hη1
  have hlow := loadTolerance_polynomial η hη hη1
  calc
    _ ≤ 10 * scheduledWeightCap b η / loadTolerance η :=
      div_le_div_of_nonneg_right (by nlinarith) htol.le
    _ ≤ 10 * (2 ^ 17 * (b + 1) / η ^ 16) / (η ^ 43 / 2 ^ 65) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left hcap (by norm_num))
        (by positivity) hlow
    _ = 10 * 2 ^ 82 * (b + 1) / η ^ 59 := by field_simp
    _ ≤ 2 ^ 86 * (b + 1) / η ^ 59 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ ≤ packingPolynomial b η / 2 := by
      simpa only [pow_one] using
        monomial_le_half_packingPolynomial b η hb.le hη hη1 86 1 59
          (by omega) (by omega) (by omega)

/-- Uniform polynomial growth of the complete explicit nibble threshold. -/
theorem packingThreshold_cast_le (b η : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    (packingThreshold b η : ℝ) ≤ packingPolynomial b η := by
  have htwo := packingPolynomial_two_le b η hb.le hη hη1
  have h1 : 1 ≤ packingPolynomial b η := by linarith
  have ht : (tailThreshold (commonRate b η) 2560 8 : ℝ) ^ 4 ≤ packingPolynomial b η := by
    have := tailFourth_le_half_packingPolynomial b η hb hη hη1
    linarith
  have hγ := scheduleGamma_pos η hη
  have hB := scheduledWeightCap_pos b η hb
  have htol := loadTolerance_pos η hη hη1
  have hw := rounding_below_packingPolynomial b η
    (4 * scheduleGamma η * scheduledWeightCap b η) hb.le hη hη1 (by positivity)
      (roundWeight_le_half_packingPolynomial b η hb hη hη1)
  have hi := rounding_below_packingPolynomial b η
    (10 * scheduleGamma η * scheduledWeightCap b η / loadTolerance η)
      hb.le hη hη1 (by positivity)
      (iterationWeight_le_half_packingPolynomial b η hb hη hη1)
  simp only [packingThreshold, physicalRoundThreshold, failureThreshold,
    Nat.cast_max, Nat.cast_pow, Nat.cast_one, max_le_iff]
  exact ⟨⟨⟨⟨⟨h1, ht⟩, h1⟩, hw⟩, h1⟩, hi⟩

theorem packingThreshold_le_ceil (b η : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    packingThreshold b η ≤ ⌈packingPolynomial b η⌉₊ := by
  have h := (packingThreshold_cast_le b η hb hη hη1).trans (Nat.le_ceil _)
  exact_mod_cast h

#print axioms tailThreshold_real_le
#print axioms tailFourth_le_half_packingPolynomial
#print axioms packingThreshold_cast_le
#print axioms packingThreshold_le_ceil

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
