/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveAverage
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

@[expose] public section

/-!
# Coupling opposite signed occurrences before their physical placement

For nonnegative masses `p_i` and `q_j`, set
`alpha_ij = p_i*q_j / max(sum p, sum q)`.
Every row and column uses at most its available mass, the total paired mass
is the smaller total, and the total unpaired mass is the absolute difference.
Thus the pairing can be fixed on abstract occurrences before any auxiliary
vertices are sampled.  This avoids changing coefficients after sampling.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

theorem product_div_max (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x * y / max x y = min x y := by
  rcases le_total x y with h | h
  · rw [max_eq_right h, min_eq_left h]
    by_cases hz : y = 0
    · have hxz : x = 0 := by linarith
      simp [hz, hxz]
    · exact mul_div_cancel_right₀ _ hz
  · rw [max_eq_left h, min_eq_right h]
    by_cases hz : x = 0
    · have hyz : y = 0 := by linarith
      simp [hz, hyz]
    · exact mul_div_cancel_left₀ _ hz

theorem div_max_le_one (x y : ℝ) (hx : 0 ≤ x) (_hy : 0 ≤ y) :
    y / max x y ≤ 1 := by
  by_cases h : max x y = 0
  · rw [h, div_zero]
    norm_num
  · have hd : 0 < max x y := lt_of_le_of_ne (le_trans hx (le_max_left _ _)) (Ne.symm h)
    rw [div_le_iff₀ hd, one_mul]
    exact le_max_right _ _

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def coupling (p : I → ℝ) (q : J → ℝ) (i : I) (j : J) : ℝ :=
  p i * q j / max (∑ i : I, p i) (∑ j : J, q j)

theorem coupling_nonneg (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (i : I) (j : J) :
    0 ≤ coupling p q i j := by
  unfold coupling
  exact div_nonneg (mul_nonneg (hp i) (hq j))
    ((sum_nonneg fun i _ => hp i).trans (le_max_left _ _))

theorem coupling_row (p : I → ℝ) (q : J → ℝ) (i : I) :
    (∑ j : J, coupling p q i j) =
      p i * ((∑ j : J, q j) / max (∑ i : I, p i) (∑ j : J, q j)) := by
  simp only [coupling, ← sum_div, ← mul_sum, mul_div_assoc]

theorem coupling_column (p : I → ℝ) (q : J → ℝ) (j : J) :
    (∑ i : I, coupling p q i j) =
      q j * ((∑ i : I, p i) / max (∑ i : I, p i) (∑ j : J, q j)) := by
  simp only [coupling, ← sum_div, ← sum_mul]
  ring

theorem coupling_row_le (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (i : I) :
    (∑ j : J, coupling p q i j) ≤ p i := by
  rw [coupling_row]
  have h := mul_le_mul_of_nonneg_left
    (div_max_le_one (∑ i : I, p i) (∑ j : J, q j)
      (sum_nonneg fun i _ => hp i) (sum_nonneg fun j _ => hq j)) (hp i)
  simpa using h

theorem coupling_column_le (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) (j : J) :
    (∑ i : I, coupling p q i j) ≤ q j := by
  rw [coupling_column]
  have h := mul_le_mul_of_nonneg_left
    (div_max_le_one (∑ j : J, q j) (∑ i : I, p i)
      (sum_nonneg fun j _ => hq j) (sum_nonneg fun i _ => hp i)) (hq j)
  simpa only [max_comm, mul_one] using h

theorem coupling_total (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) :
    (∑ i : I, ∑ j : J, coupling p q i j) =
      min (∑ i : I, p i) (∑ j : J, q j) := by
  simp_rw [coupling_row]
  rw [← sum_mul, ← mul_div_assoc]
  exact product_div_max _ _ (sum_nonneg fun i _ => hp i) (sum_nonneg fun j _ => hq j)

/-- Both remainders are nonnegative and their combined mass is exactly the imbalance. -/
theorem coupling_remainders (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j) :
    (∀ i, 0 ≤ p i - ∑ j : J, coupling p q i j) ∧
    (∀ j, 0 ≤ q j - ∑ i : I, coupling p q i j) ∧
    ((∑ i : I, (p i - ∑ j : J, coupling p q i j)) +
      (∑ j : J, (q j - ∑ i : I, coupling p q i j))) =
      |(∑ i : I, p i) - (∑ j : J, q j)| := by
  refine ⟨fun i => sub_nonneg.mpr (coupling_row_le p q hp hq i),
    fun j => sub_nonneg.mpr (coupling_column_le p q hp hq j), ?_⟩
  rw [sum_sub_distrib, sum_sub_distrib,
    sum_comm (s := (univ : Finset J)) (t := (univ : Finset I)),
    coupling_total p q hp hq]
  rcases le_total (∑ i : I, p i) (∑ j : J, q j) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

/-- Splitting every coefficient into its unpaired and paired masses is an
exact identity for arbitrary evaluations. Pairing is fixed before averaging. -/
theorem coupling_evaluation (p f : I → ℝ) (q g : J → ℝ) :
    (∑ i : I, p i * f i) - (∑ j : J, q j * g j) =
      (∑ i : I, (p i - ∑ j : J, coupling p q i j) * f i) -
      (∑ j : J, (q j - ∑ i : I, coupling p q i j) * g j) +
      ∑ i : I, ∑ j : J, coupling p q i j * (f i - g j) := by
  simp only [sub_mul, mul_sub, sum_sub_distrib, sum_mul]
  rw [sum_comm (s := (univ : Finset J)) (t := (univ : Finset I))]
  ring

/-- If the signed boundary at an old edge vanishes, every unpaired mass there
vanishes. This is what removes all non-host old edges after coupling. -/
theorem coupling_remainders_zero (p : I → ℝ) (q : J → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ j, 0 ≤ q j)
    (hbal : (∑ i : I, p i) = ∑ j : J, q j) :
    (∀ i, p i - ∑ j : J, coupling p q i j = 0) ∧
    (∀ j, q j - ∑ i : I, coupling p q i j = 0) := by
  obtain ⟨hr, hc, hmass⟩ := coupling_remainders p q hp hq
  rw [hbal, sub_self, abs_zero] at hmass
  have hs₁ : 0 ≤ ∑ i : I, (p i - ∑ j : J, coupling p q i j) :=
    sum_nonneg fun i _ => hr i
  have hs₂ : 0 ≤ ∑ j : J, (q j - ∑ i : I, coupling p q i j) :=
    sum_nonneg fun j _ => hc j
  constructor
  · intro i
    have hle : p i - ∑ j : J, coupling p q i j ≤
        ∑ k : I, (p k - ∑ j : J, coupling p q k j) :=
      single_le_sum (fun k _ => hr k) (mem_univ i)
    linarith [hr i]
  · intro j
    have hle : q j - ∑ i : I, coupling p q i j ≤
        ∑ k : J, (q k - ∑ i : I, coupling p q i k) :=
      single_le_sum (fun k _ => hc k) (mem_univ j)
    linarith [hc j]

#print axioms product_div_max
#print axioms coupling_nonneg
#print axioms coupling_row_le
#print axioms coupling_column_le
#print axioms coupling_total
#print axioms coupling_remainders
#print axioms coupling_evaluation
#print axioms coupling_remainders_zero

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
