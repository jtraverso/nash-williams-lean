/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests

/-!
# Quantitative concentration for the decomposable reserve

The common-neighbour statistic is a sum of two-block indicators. Its total
coordinate influence is at most twice the number of witnesses. In a triangle
packing each individual block affects at most two witnesses; these facts give
the variance bound without imposing independence between the witnesses.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {m : ℕ}

theorem pairCount_influence_sum {W : Type*} (s : Finset W) (a b : W → Fin m) :
    (∑ i : Fin m, ((s.filter fun w => a w = i ∨ b w = i).card : ℝ)) ≤
      2 * s.card := by
  classical
  simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [sum_comm]
  calc
    _ ≤ ∑ w ∈ s, ∑ i : Fin m,
        ((if a w = i then (1 : ℝ) else 0) + (if b w = i then (1 : ℝ) else 0)) := by
      apply sum_le_sum
      intro w _
      apply sum_le_sum
      intro i _
      by_cases ha : a w = i <;> by_cases hb : b w = i <;> simp [ha, hb]
    _ = 2 * s.card := by simp [sum_add_distrib, eq_comm]; ring

theorem pairCount_variance {W : Type*} (s : Finset W) (a b : W → Fin m)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hc : ∀ i, (s.filter fun w => a w = i ∨ b w = i).card ≤ 2) :
    (∑ i : Fin m, ρ * (((s.filter fun w => a w = i ∨ b w = i).card : ℝ) ^ 2)) ≤
      4 * ρ * s.card := by
  classical
  calc
    _ ≤ ∑ i : Fin m, (2 * ρ) * ((s.filter fun w => a w = i ∨ b w = i).card : ℝ) := by
      apply sum_le_sum
      intro i _
      have hci0 : 0 ≤ ((s.filter fun w => a w = i ∨ b w = i).card : ℝ) := by positivity
      have hci2 : ((s.filter fun w => a w = i ∨ b w = i).card : ℝ) ≤ 2 := by
        exact_mod_cast hc i
      have hsq : ((s.filter fun w => a w = i ∨ b w = i).card : ℝ) ^ 2 ≤
          2 * ((s.filter fun w => a w = i ∨ b w = i).card : ℝ) := by nlinarith
      calc _ ≤ ρ * (2 * ((s.filter fun w => a w = i ∨ b w = i).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hsq hρ
      _ = _ := by ring
    _ = (2 * ρ) * ∑ i : Fin m,
        ((s.filter fun w => a w = i ∨ b w = i).card : ℝ) := by rw [mul_sum]
    _ ≤ (2 * ρ) * (2 * s.card) :=
      mul_le_mul_of_nonneg_left (pairCount_influence_sum s a b) (by positivity)
    _ = _ := by ring

/-- Uniform lower tail for the surviving common-neighbour witnesses. -/
theorem pairCount_lower_tail {W : Type*} (s : Finset W) (a b : W → Fin m)
    (ρ ω n : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 0 < n) (hsize : (s.card : ℝ) ≤ n)
    (hwitness : 3 * ω * n / 4 ≤ (s.card : ℝ))
    (hc : ∀ i, (s.filter fun w => a w = i ∨ b w = i).card ≤ 2) :
    cubeProb (fun _ : Fin m => ρ)
      (fun x => pairCount s a b x < ρ ^ 2 * ω * n / 4) ≤
        Real.exp (-(ρ ^ 3 * ω ^ 2 * n / 48)) := by
  classical
  let c : Fin m → ℝ := fun i => (s.filter fun w => a w = i ∨ b w = i).card
  let u : ℝ := ρ ^ 2 * ω * n / 2
  have hu : 0 < u := by dsimp [u]; positivity
  have hq : ∀ _i : Fin m, 0 ≤ ρ ∧ ρ ≤ 1 := fun _ => ⟨hρ.le, hρ1⟩
  have hc' : ∀ i, 0 ≤ c i ∧ c i ≤ 2 := by
    intro i
    constructor
    · dsimp [c]; positivity
    · dsimp [c]; exact_mod_cast hc i
  have hmean := pairCount_mean_ge ρ hρ.le hρ1 s a b
  have hlow : 3 * (ρ ^ 2 * ω * n) / 4 ≤ cubeMean (fun _ : Fin m => ρ) (pairCount s a b) := by
    have hm := mul_le_mul_of_nonneg_left hwitness (sq_nonneg ρ)
    nlinarith only [hmean, hm]
  have hsub : ∀ x, pairCount s a b x < ρ ^ 2 * ω * n / 4 →
      u ≤ cubeMean (fun _ : Fin m => ρ) (pairCount s a b) - pairCount s a b x := by
    intro x hx
    dsimp [u]
    linarith only [hlow, hx]
  have hvar : (∑ i : Fin m, ρ * c i ^ 2) ≤ 4 * ρ * n := by
    exact (pairCount_variance s a b ρ hρ.le hc).trans
      (mul_le_mul_of_nonneg_left hsize (by positivity))
  have hvar0 : 0 ≤ ∑ i : Fin m, ρ * c i ^ 2 :=
    sum_nonneg fun _ _ => mul_nonneg hρ.le (sq_nonneg _)
  have hρω : ρ ^ 2 * ω ≤ ρ := by
    have hs : ρ ^ 2 ≤ ρ := by nlinarith only [hρ.le, hρ1]
    have ht := mul_le_mul_of_nonneg_left hω1 (sq_nonneg ρ)
    nlinarith only [hs, ht]
  have huupper : u ≤ ρ * n := by
    have ht := mul_le_mul_of_nonneg_right hρω hn.le
    dsimp [u]
    nlinarith only [ht, mul_nonneg hρ.le hn.le]
  have hden : 0 < 2 * ((∑ i : Fin m, ρ * c i ^ 2) + 2 * u) := by
    linarith only [hu, hvar0]
  have hdenupper : 2 * ((∑ i : Fin m, ρ * c i ^ 2) + 2 * u) ≤ 12 * ρ * n := by
    linarith only [hvar, huupper]
  have hratio : ρ ^ 3 * ω ^ 2 * n / 48 ≤
      u ^ 2 / (2 * ((∑ i : Fin m, ρ * c i ^ 2) + 2 * u)) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (ρ ^ 3 * ω ^ 2 * n / 48) * (12 * ρ * n) :=
        mul_le_mul_of_nonneg_left hdenupper (by positivity)
      _ = u ^ 2 := by dsimp [u]; ring
  calc
    _ ≤ cubeProb (fun _ : Fin m => ρ)
        (fun x => u ≤ cubeMean (fun _ : Fin m => ρ) (pairCount s a b) - pairCount s a b x) :=
      cubeProb_mono _ hq hsub
    _ ≤ Real.exp (-(u ^ 2 / (2 * ((∑ i : Fin m, ρ * c i ^ 2) + 2 * u)))) :=
      cube_lower_tail _ hq _ c 2 (by norm_num) hc' (pairCount_coordinate s a b) u hu
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg hratio)

#print axioms pairCount_influence_sum
#print axioms pairCount_variance
#print axioms pairCount_lower_tail

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests
