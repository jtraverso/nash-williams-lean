/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedQuantitative.EffectiveTail
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# A polynomially bounded nibble schedule

The schedule has the two conclusions used by the existing `IterInv`:
exponential degree decrease and small accumulated conflict waste. Unlike
an existence-only schedule, its round count, weight amplification and load
error denominator are bounded by explicit powers of the target error.
-/

namespace KeevashQuantitative

noncomputable def scheduleGamma (η : ℝ) : ℝ := η ^ 2 / 65536

noncomputable def scheduleRounds (η : ℝ) : ℕ :=
  ⌈8 * Real.log (2 / η) / scheduleGamma η⌉₊

theorem exp_half_le_two : Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have h := Real.exp_bound_div_one_sub_of_interval
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at h ⊢
  exact h

theorem scheduleGamma_pos (η : ℝ) (hη : 0 < η) : 0 < scheduleGamma η := by
  unfold scheduleGamma
  positivity

theorem scheduleGamma_le (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    scheduleGamma η ≤ 1 / 128 := by
  have hsq : η ^ 2 ≤ 1 := by nlinarith
  unfold scheduleGamma
  linarith

theorem schedule_log_pos (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < Real.log (2 / η) := by
  apply Real.log_pos
  rw [lt_div_iff₀ hη]
  linarith

theorem schedule_rounds_pos (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    1 ≤ scheduleRounds η := by
  have hlog := schedule_log_pos η hη hη1
  have hγ := scheduleGamma_pos η hη
  have hceil := Nat.le_ceil (8 * Real.log (2 / η) / scheduleGamma η)
  have hpos : (0 : ℝ) < scheduleRounds η := lt_of_lt_of_le (by positivity) hceil
  have : 0 < scheduleRounds η := by exact_mod_cast hpos
  omega

theorem schedule_rounds_gamma (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (scheduleRounds η : ℝ) * scheduleGamma η ≤
      8 * Real.log (2 / η) + scheduleGamma η := by
  have hlog := schedule_log_pos η hη hη1
  have hγ := scheduleGamma_pos η hη
  have hceil := Nat.ceil_lt_add_one
    (show 0 ≤ 8 * Real.log (2 / η) / scheduleGamma η by positivity)
  have h := mul_lt_mul_of_pos_right hceil hγ
  rw [add_mul, div_mul_cancel₀ _ hγ.ne'] at h
  simpa only [scheduleRounds, one_mul] using h.le

theorem schedule_decay (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (1 - scheduleGamma η / 8) ^ scheduleRounds η ≤ η / 2 := by
  have hγ := scheduleGamma_pos η hη
  have hγ1 := scheduleGamma_le η hη hη1
  have hceil := Nat.le_ceil (8 * Real.log (2 / η) / scheduleGamma η)
  have h1 : 1 - scheduleGamma η / 8 ≤ Real.exp (-(scheduleGamma η / 8)) := by
    have := Real.add_one_le_exp (-(scheduleGamma η / 8))
    linarith
  have h2 := pow_le_pow_left₀ (by linarith : 0 ≤ 1 - scheduleGamma η / 8)
    h1 (scheduleRounds η)
  rw [← Real.exp_nat_mul] at h2
  have h3 : Real.log (2 / η) ≤
      (scheduleRounds η : ℝ) * (scheduleGamma η / 8) := by
    rw [div_le_iff₀ hγ] at hceil
    change 8 * Real.log (2 / η) ≤ (scheduleRounds η : ℝ) * scheduleGamma η at hceil
    linarith
  have h4 : Real.exp (-Real.log (2 / η)) = η / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]
    field_simp
  calc
    _ ≤ Real.exp ((scheduleRounds η : ℝ) * -(scheduleGamma η / 8)) := h2
    _ ≤ Real.exp (-Real.log (2 / η)) := Real.exp_le_exp.mpr (by linarith)
    _ = η / 2 := h4

theorem schedule_waste (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    24 * (scheduleRounds η : ℝ) * scheduleGamma η ^ 2 ≤ η / 4 := by
  have hγ := scheduleGamma_pos η hη
  have hγ1 := scheduleGamma_le η hη hη1
  have hround := schedule_rounds_gamma η hη hη1
  have hlog : Real.log (2 / η) ≤ 2 / η :=
    (Real.log_le_sub_one_of_pos (by positivity : 0 < 2 / η)).trans (by linarith)
  have hbound := mul_le_mul_of_nonneg_right hround (show 0 ≤ 24 * scheduleGamma η by positivity)
  have hlogmul := mul_le_mul_of_nonneg_right hlog
    (show 0 ≤ 192 * scheduleGamma η by positivity)
  have hγformula : 65536 * scheduleGamma η = η ^ 2 := by
    unfold scheduleGamma
    ring
  have hratio : scheduleGamma η / η = η / 65536 := by
    unfold scheduleGamma
    field_simp
  have hsq : scheduleGamma η ^ 2 ≤ scheduleGamma η / 128 := by nlinarith
  have hηsq : η ^ 2 ≤ η := by nlinarith
  have hlogbound : 192 * scheduleGamma η * Real.log (2 / η) ≤ 384 * η / 65536 := by
    calc
      _ ≤ (2 / η) * (192 * scheduleGamma η) := by nlinarith only [hlogmul]
      _ = 384 * η / 65536 := by
        calc
          _ = 384 * (scheduleGamma η / η) := by ring
          _ = _ := by rw [hratio]; ring
  nlinarith only [hbound, hlogbound, hsq, hγformula, hηsq]

/-- The number of rounds grows at most cubically in the inverse target error. -/
theorem schedule_rounds_polynomial (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (scheduleRounds η : ℝ) ≤ 2 ^ 21 / η ^ 3 := by
  have hround := schedule_rounds_gamma η hη hη1
  have hlog : Real.log (2 / η) ≤ 2 / η :=
    (Real.log_le_sub_one_of_pos (by positivity : 0 < 2 / η)).trans (by linarith)
  have hlogη : Real.log (2 / η) * η ≤ 2 := (le_div_iff₀ hη).mp hlog
  have hmul := mul_le_mul_of_nonneg_right hround hη.le
  have hηcube : η ^ 3 ≤ 1 := pow_le_one₀ hη.le hη1
  dsimp [scheduleGamma] at hmul
  rw [le_div_iff₀ (pow_pos hη 3)]
  norm_num
  nlinarith only [hmul, hlogη, hηcube]

/-- The accumulated weight rescaling has an explicit polynomial bound. -/
theorem schedule_weight_growth (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    Real.exp (2 * scheduleGamma η * scheduleRounds η) ≤ 2 ^ 17 / η ^ 16 := by
  have hround := schedule_rounds_gamma η hη hη1
  have hγ1 := scheduleGamma_le η hη hη1
  have harg : 2 * scheduleGamma η * scheduleRounds η ≤
      16 * Real.log (2 / η) + 1 / 2 := by nlinarith only [hround, hγ1]
  have he16 : Real.exp (16 * Real.log (2 / η)) = Real.exp (Real.log (2 / η)) ^ 16 := by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (2 / η)) 16
  calc
    _ ≤ Real.exp (16 * Real.log (2 / η) + 1 / 2) := Real.exp_le_exp.mpr harg
    _ = (2 / η) ^ 16 * Real.exp (1 / 2) := by
      rw [Real.exp_add, he16, Real.exp_log (by positivity)]
    _ ≤ (2 / η) ^ 16 * 2 :=
      mul_le_mul_of_nonneg_left exp_half_le_two (by positivity)
    _ = 2 ^ 17 / η ^ 16 := by rw [div_pow]; ring

/-- The load-error amplification has an explicit polynomial bound as well. -/
theorem schedule_load_growth (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    (1 + 5 * scheduleGamma η) ^ scheduleRounds η ≤ 2 ^ 41 / η ^ 40 := by
  have hγ := scheduleGamma_pos η hη
  have hγ1 := scheduleGamma_le η hη hη1
  have hround := schedule_rounds_gamma η hη hη1
  have harg : (scheduleRounds η : ℝ) * (5 * scheduleGamma η) ≤
      40 * Real.log (2 / η) + 1 / 2 := by nlinarith only [hround, hγ1]
  have he40 : Real.exp (40 * Real.log (2 / η)) = Real.exp (Real.log (2 / η)) ^ 40 := by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (Real.log (2 / η)) 40
  have hbase : 1 + 5 * scheduleGamma η ≤ Real.exp (5 * scheduleGamma η) := by
    have := Real.add_one_le_exp (5 * scheduleGamma η)
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + 5 * scheduleGamma η)
    hbase (scheduleRounds η)
  rw [← Real.exp_nat_mul] at hpow
  calc
    _ ≤ Real.exp ((scheduleRounds η : ℝ) * (5 * scheduleGamma η)) := hpow
    _ ≤ Real.exp (40 * Real.log (2 / η) + 1 / 2) := Real.exp_le_exp.mpr harg
    _ = (2 / η) ^ 40 * Real.exp (1 / 2) := by
      rw [Real.exp_add, he40, Real.exp_log (by positivity)]
    _ ≤ (2 / η) ^ 40 * 2 :=
      mul_le_mul_of_nonneg_left exp_half_le_two (by positivity)
    _ = 2 ^ 41 / η ^ 40 := by rw [div_pow]; ring

noncomputable def loadTolerance (η : ℝ) : ℝ :=
  1 / (8 * scheduleRounds η * (1 + 5 * scheduleGamma η) ^ scheduleRounds η)

theorem loadTolerance_pos (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < loadTolerance η := by
  have hγ := scheduleGamma_pos η hη
  have hr := schedule_rounds_pos η hη hη1
  have hrR : (0 : ℝ) < scheduleRounds η := by exact_mod_cast (by omega : 0 < scheduleRounds η)
  unfold loadTolerance
  positivity

/-- The admissible load tolerance is bounded below by a fixed power of `η`. -/
theorem loadTolerance_polynomial (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    η ^ 43 / 2 ^ 65 ≤ loadTolerance η := by
  have hγ := scheduleGamma_pos η hη
  have hr := schedule_rounds_pos η hη hη1
  have hrR : (0 : ℝ) < scheduleRounds η := by exact_mod_cast (by omega : 0 < scheduleRounds η)
  have hdenom : 0 < 8 * (scheduleRounds η : ℝ) *
      (1 + 5 * scheduleGamma η) ^ scheduleRounds η := by positivity
  have hb := mul_le_mul (schedule_rounds_polynomial η hη hη1)
    (schedule_load_growth η hη hη1) (by positivity) (by positivity)
  have hdenomBound : 8 * (scheduleRounds η : ℝ) *
      (1 + 5 * scheduleGamma η) ^ scheduleRounds η ≤ 2 ^ 65 / η ^ 43 := by
    calc
      _ ≤ 8 * ((2 ^ 21 / η ^ 3) * (2 ^ 41 / η ^ 40)) := by nlinarith only [hb]
      _ = 2 ^ 65 / η ^ 43 := by
        rw [div_mul_div_comm, ← pow_add]
        norm_num
        ring
  unfold loadTolerance
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ 65) hdenom]
  have h := (le_div_iff₀ (pow_pos hη 43)).mp hdenomBound
  simpa only [one_mul, mul_comm] using h

#print axioms exp_half_le_two
#print axioms scheduleGamma_pos
#print axioms scheduleGamma_le
#print axioms schedule_log_pos
#print axioms schedule_rounds_pos
#print axioms schedule_rounds_gamma
#print axioms schedule_decay
#print axioms schedule_waste
#print axioms schedule_rounds_polynomial
#print axioms schedule_weight_growth
#print axioms schedule_load_growth
#print axioms loadTolerance_pos
#print axioms loadTolerance_polynomial

end KeevashQuantitative
