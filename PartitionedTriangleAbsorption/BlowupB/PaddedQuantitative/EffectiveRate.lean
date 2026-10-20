/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedQuantitative.EffectiveSchedule

/-!
# One polynomial rate for all nine nibble failure terms

The nine displayed inequalities are exactly the rate hypotheses in the
original `Nibble.Asymptotic.eventually_failBound_lt_one`.  This file avoids
its non-effective choice of a positive minimum.  The weight cap includes
all rounds of the schedule, so the same rate works at every round.
-/

namespace KeevashQuantitative

noncomputable def scheduledWeightCap (b η : ℝ) : ℝ :=
  b * Real.exp (2 * scheduleGamma η * scheduleRounds η)

noncomputable def roundEpsilon (η : ℝ) : ℝ := loadTolerance η / 2

noncomputable def commonRate (b η : ℝ) : ℝ :=
  η ^ 102 / (2 ^ 160 * (b + 1))

theorem scheduledWeightCap_pos (b η : ℝ) (hb : 0 < b) :
    0 < scheduledWeightCap b η := by
  unfold scheduledWeightCap
  positivity

theorem scheduledWeightCap_polynomial (b η : ℝ) (hb : 0 ≤ b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    scheduledWeightCap b η ≤ 2 ^ 17 * (b + 1) / η ^ 16 := by
  have hw := mul_le_mul_of_nonneg_left (schedule_weight_growth η hη hη1) hb
  have hscale : 0 ≤ 2 ^ 17 / η ^ 16 := by positivity
  calc
    _ ≤ b * (2 ^ 17 / η ^ 16) := hw
    _ ≤ (b + 1) * (2 ^ 17 / η ^ 16) :=
      mul_le_mul_of_nonneg_right (by linarith) hscale
    _ = _ := by ring

theorem loadTolerance_le_eighth (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    loadTolerance η ≤ 1 / 8 := by
  have hγ := scheduleGamma_pos η hη
  have hr := schedule_rounds_pos η hη hη1
  have hrR : (1 : ℝ) ≤ scheduleRounds η := by exact_mod_cast hr
  have hgrowth : 1 ≤ (1 + 5 * scheduleGamma η) ^ scheduleRounds η :=
    one_le_pow₀ (by linarith)
  have hden : (8 : ℝ) ≤ 8 * scheduleRounds η *
      (1 + 5 * scheduleGamma η) ^ scheduleRounds η := by nlinarith
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden

theorem roundEpsilon_pos (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    0 < roundEpsilon η := by
  exact div_pos (loadTolerance_pos η hη hη1) (by norm_num)

theorem roundEpsilon_half_bounds (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    η ^ 43 / 2 ^ 67 ≤ roundEpsilon η / 2 ∧ roundEpsilon η / 2 ≤ 1 := by
  have hlow := loadTolerance_polynomial η hη hη1
  have hupp := loadTolerance_le_eighth η hη hη1
  unfold roundEpsilon
  constructor <;> norm_num at * <;> linarith

theorem commonRate_pos (b η : ℝ) (hb : 0 ≤ b) (hη : 0 < η) :
    0 < commonRate b η := by
  unfold commonRate
  positivity

theorem commonRate_le_monomial (b η : ℝ) (hb : 0 ≤ b)
    (hη : 0 < η) (hη1 : η ≤ 1) (k d : ℕ) (hk : k ≤ 102) (hd : d ≤ 160) :
    commonRate b η ≤ η ^ k / (2 ^ d * (b + 1)) := by
  have hnum := pow_le_pow_of_le_one hη.le hη1 hk
  have hpow : (2 : ℝ) ^ d ≤ 2 ^ 160 := pow_le_pow_right₀ (by norm_num) hd
  unfold commonRate
  exact div_le_div₀ (by positivity) hnum (by positivity)
    (mul_le_mul_of_nonneg_right hpow (by positivity))

theorem commonRate_le_unweighted (b η : ℝ) (hb : 0 ≤ b)
    (hη : 0 < η) (hη1 : η ≤ 1) (k d : ℕ) (hk : k ≤ 102) (hd : d ≤ 160) :
    commonRate b η ≤ η ^ k / 2 ^ d := by
  apply (commonRate_le_monomial b η hb hη hη1 k d hk hd).trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have hpow : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith

/-- The single displayed monomial is below each of the original nine rates. -/
theorem commonRate_bounds (b η : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hη1 : η ≤ 1) :
    let γ := scheduleGamma η
    let θ := η / 2
    let B := scheduledWeightCap b η
    let ε := roundEpsilon η
    let c := commonRate b η
    c ≤ γ * θ / 64 ∧
    c ≤ θ / (24576 * B * (γ + 1 / 64)) ∧
    c ≤ γ * θ / 128 ∧
    c ≤ γ * θ / 4704 ∧
    c ≤ γ / (12 * B) ∧
    c ≤ γ ^ 2 / 2 ∧
    c ≤ γ ^ 3 / 4 ∧
    c ≤ 1 / 8 ∧
    c ≤ (ε / 2) ^ 2 / (2 * (10 * B * γ + 3 * B * (ε / 2))) := by
  dsimp only
  let γ := scheduleGamma η
  let B := scheduledWeightCap b η
  let ε := roundEpsilon η
  have hγ : 0 < γ := scheduleGamma_pos η hη
  have hγ1 : γ ≤ 1 := (scheduleGamma_le η hη hη1).trans (by norm_num)
  have hγsmall : γ + 1 / 64 ≤ 1 := by
    have := scheduleGamma_le η hη hη1
    change γ ≤ 1 / 128 at this
    linarith
  have hB : 0 < B := scheduledWeightCap_pos b η hb
  have hBbound : B ≤ 2 ^ 17 * (b + 1) / η ^ 16 :=
    scheduledWeightCap_polynomial b η hb.le hη hη1
  rw [mul_div_assoc] at hBbound
  have hε : 0 < ε := roundEpsilon_pos η hη hη1
  obtain ⟨hεlow, hε1⟩ := roundEpsilon_half_bounds η hη hη1
  change η ^ 43 / 2 ^ 67 ≤ ε / 2 at hεlow
  change ε / 2 ≤ 1 at hε1
  have mon (k d : ℕ) (hk : k ≤ 102) (hd : d ≤ 160) :=
    commonRate_le_monomial b η hb.le hη hη1 k d hk hd
  have bare (k d : ℕ) (hk : k ≤ 102) (hd : d ≤ 160) :=
    commonRate_le_unweighted b η hb.le hη hη1 k d hk hd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc
      _ ≤ η ^ 3 / 2 ^ 23 := bare 3 23 (by omega) (by omega)
      _ = _ := by unfold scheduleGamma; ring
  · have hden : 24576 * B * (γ + 1 / 64) ≤ 2 ^ 32 * (b + 1) / η ^ 16 := by
      rw [mul_div_assoc]
      have hfirst := mul_le_mul_of_nonneg_left hγsmall (show 0 ≤ 24576 * B by positivity)
      have hsecond := mul_le_mul_of_nonneg_left hBbound (by norm_num : (0 : ℝ) ≤ 24576)
      have hratio : 0 ≤ (b + 1) / η ^ 16 := by positivity
      norm_num at hfirst hsecond ⊢
      nlinarith only [hfirst, hsecond, hratio]
    calc
      _ ≤ η ^ 17 / (2 ^ 33 * (b + 1)) := mon 17 33 (by omega) (by omega)
      _ = (η / 2) / (2 ^ 32 * (b + 1) / η ^ 16) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  · calc
      _ ≤ η ^ 3 / 2 ^ 24 := bare 3 24 (by omega) (by omega)
      _ = _ := by unfold scheduleGamma; ring
  · calc
      _ ≤ η ^ 3 / 2 ^ 30 := bare 3 30 (by omega) (by omega)
      _ ≤ _ := by
        unfold scheduleGamma
        have hp : 0 ≤ η ^ 3 := by positivity
        norm_num
        nlinarith only [hp]
  · have hden : 12 * B ≤ 2 ^ 21 * (b + 1) / η ^ 16 := by
      rw [mul_div_assoc]
      have hsecond := mul_le_mul_of_nonneg_left hBbound (by norm_num : (0 : ℝ) ≤ 12)
      have hratio : 0 ≤ (b + 1) / η ^ 16 := by positivity
      norm_num at hsecond ⊢
      nlinarith only [hsecond, hratio]
    calc
      _ ≤ η ^ 18 / (2 ^ 37 * (b + 1)) := mon 18 37 (by omega) (by omega)
      _ = γ / (2 ^ 21 * (b + 1) / η ^ 16) := by dsimp [γ, scheduleGamma]; field_simp; ring
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  · calc
      _ ≤ η ^ 4 / 2 ^ 33 := bare 4 33 (by omega) (by omega)
      _ = _ := by unfold scheduleGamma; ring
  · calc
      _ ≤ η ^ 6 / 2 ^ 50 := bare 6 50 (by omega) (by omega)
      _ = _ := by unfold scheduleGamma; ring
  · simpa using (show commonRate b η ≤ 1 / 8 by
      convert bare 0 3 (by omega) (by omega) using 1; norm_num)
  · have hnum : η ^ 86 / 2 ^ 134 ≤ (ε / 2) ^ 2 := by
      have hp := pow_le_pow_left₀ (by positivity : 0 ≤ η ^ 43 / 2 ^ 67) hεlow 2
      convert hp using 1; ring
    have hden : 2 * (10 * B * γ + 3 * B * (ε / 2)) ≤
        2 ^ 22 * (b + 1) / η ^ 16 := by
      rw [mul_div_assoc]
      have hfirst := mul_le_mul_of_nonneg_left hγ1 (show 0 ≤ 10 * B by positivity)
      have hsecond := mul_le_mul_of_nonneg_left hε1 (show 0 ≤ 3 * B by positivity)
      have hthird := mul_le_mul_of_nonneg_left hBbound (by norm_num : (0 : ℝ) ≤ 32)
      norm_num at hfirst hsecond hthird ⊢
      nlinarith only [hfirst, hsecond, hthird, hB]
    calc
      _ ≤ η ^ 102 / (2 ^ 156 * (b + 1)) := mon 102 156 (by omega) (by omega)
      _ = (η ^ 86 / 2 ^ 134) / (2 ^ 22 * (b + 1) / η ^ 16) := by field_simp
      _ ≤ (ε / 2) ^ 2 / (2 ^ 22 * (b + 1) / η ^ 16) :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden

#print axioms scheduledWeightCap_pos
#print axioms scheduledWeightCap_polynomial
#print axioms loadTolerance_le_eighth
#print axioms roundEpsilon_pos
#print axioms roundEpsilon_half_bounds
#print axioms commonRate_pos
#print axioms commonRate_le_monomial
#print axioms commonRate_le_unweighted
#print axioms commonRate_bounds

end KeevashQuantitative
