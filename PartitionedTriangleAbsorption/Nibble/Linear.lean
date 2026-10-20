/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.CubeTools

/-! # Weighted coin sums on the cube

`lin J c ω = ∑_{i ∈ J, ω i} c i`. Its mean, bounded differences, two tails
(with an upper variance budget) and the second factorial moment of an
unweighted count.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open BernoulliExposure BernoulliConcentration Finset

variable {n : ℕ}

/-- Weighted count of retained coins of `J`. -/
def lin (J : Finset (Fin n)) (c : Fin n → ℝ) (ω : Fin n → Bool) : ℝ :=
  ∑ i ∈ J, (if ω i then c i else 0)

theorem cubeMean_lin (q : Fin n → ℝ) (J : Finset (Fin n)) (c : Fin n → ℝ) :
    cubeMean q (lin J c) = ∑ i ∈ J, q i * c i := by
  unfold lin
  rw [cubeMean_sum]
  apply sum_congr rfl
  intro i _
  have : (fun ω : Fin n → Bool => if ω i then c i else 0) =
      fun ω => c i * (if ω i then (1 : ℝ) else 0) := by
    funext ω; split_ifs <;> simp
  rw [this, cubeMean_const_mul, cubeMean_coord, mul_comm]

theorem lin_nonneg (J : Finset (Fin n)) (c : Fin n → ℝ) (hc : ∀ i ∈ J, 0 ≤ c i)
    (ω : Fin n → Bool) : 0 ≤ lin J c ω :=
  sum_nonneg fun i hi => by split_ifs; exacts [hc i hi, le_rfl]

theorem lin_indepOf (J : Finset (Fin n)) (c : Fin n → ℝ) (I : Finset (Fin n))
    (hIJ : Disjoint I J) : IndepOf I (lin J c) := by
  intro ω j b hj
  unfold lin
  apply sum_congr rfl
  intro i hi
  have : i ≠ j := fun h => Finset.disjoint_left.mp hIJ (h ▸ hj) hi
  rw [Function.update_of_ne this]

theorem lin_update_sub (J : Finset (Fin n)) (c : Fin n → ℝ) (i : Fin n) (ω : Fin n → Bool) :
    lin J c (Function.update ω i true) - lin J c (Function.update ω i false) =
      if i ∈ J then c i else 0 := by
  unfold lin
  rw [← sum_sub_distrib]
  split_ifs with hi
  · rw [sum_eq_single i]
    · simp
    · intro k _ hki
      simp [Function.update_of_ne hki]
    · intro h; exact absurd hi h
  · apply sum_eq_zero
    intro k hk
    have hki : k ≠ i := fun h => hi (h ▸ hk)
    simp [Function.update_of_ne hki]

theorem lin_coordBounded (J : Finset (Fin n)) (c : Fin n → ℝ) (hc : ∀ i ∈ J, 0 ≤ c i) :
    CoordBounded (lin J c) (fun i => if i ∈ J then c i else 0) := by
  intro i ω
  rw [lin_update_sub]
  change |if i ∈ J then c i else 0| ≤ if i ∈ J then c i else 0
  split_ifs with h
  · rw [abs_of_nonneg (hc i h)]
  · simp

/-- Monotonicity of the Bernstein exponent in the variance budget. -/
theorem bernstein_mono (t L V V' : ℝ) (hL : 0 < L) (ht : 0 < t) (hV : 0 ≤ V) (hVV : V ≤ V') :
    Real.exp (-(t ^ 2 / (2 * (V + L * t)))) ≤ Real.exp (-(t ^ 2 / (2 * (V' + L * t)))) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  linarith

theorem sum_ite_sq (J : Finset (Fin n)) (q c : Fin n → ℝ) :
    ∑ i, q i * (if i ∈ J then c i else 0) ^ 2 = ∑ i ∈ J, q i * c i ^ 2 := by
  rw [sum_congr rfl (g := fun i => if i ∈ J then q i * c i ^ 2 else 0)
    (fun i _ => by by_cases h : i ∈ J <;> simp [h]), sum_ite_mem, univ_inter]

/-- Upper tail of a weighted coin sum. -/
theorem lin_upper_tail (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (J : Finset (Fin n)) (c : Fin n → ℝ) (L V : ℝ) (hL : 0 < L)
    (hc : ∀ i ∈ J, 0 ≤ c i ∧ c i ≤ L) (hV : ∑ i ∈ J, q i * c i ^ 2 ≤ V) (t : ℝ) (ht : 0 < t) :
    cubeProb q (fun ω => (∑ i ∈ J, q i * c i) + t ≤ lin J c ω) ≤
      Real.exp (-(t ^ 2 / (2 * (V + L * t)))) := by
  have h := cube_upper_tail q hq (lin J c) (fun i => if i ∈ J then c i else 0) L hL
    (fun i => by split_ifs with h; exacts [hc i h, ⟨le_rfl, hL.le⟩])
    (lin_coordBounded J c fun i hi => (hc i hi).1) t ht
  rw [cubeMean_lin, sum_ite_sq] at h
  refine le_trans (le_of_eq ?_) (h.trans (bernstein_mono t L _ V hL ht
    (sum_nonneg fun i _ => mul_nonneg (hq i).1 (sq_nonneg _)) hV))
  congr 1
  funext ω
  apply propext
  constructor <;> intro h' <;> linarith

/-- Lower tail of a weighted coin sum. -/
theorem lin_lower_tail (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (J : Finset (Fin n)) (c : Fin n → ℝ) (L V : ℝ) (hL : 0 < L)
    (hc : ∀ i ∈ J, 0 ≤ c i ∧ c i ≤ L) (hV : ∑ i ∈ J, q i * c i ^ 2 ≤ V) (t : ℝ) (ht : 0 < t) :
    cubeProb q (fun ω => lin J c ω + t ≤ ∑ i ∈ J, q i * c i) ≤
      Real.exp (-(t ^ 2 / (2 * (V + L * t)))) := by
  have h := cube_lower_tail q hq (lin J c) (fun i => if i ∈ J then c i else 0) L hL
    (fun i => by split_ifs with h; exacts [hc i h, ⟨le_rfl, hL.le⟩])
    (lin_coordBounded J c fun i hi => (hc i hi).1) t ht
  rw [cubeMean_lin, sum_ite_sq] at h
  refine le_trans (le_of_eq ?_) (h.trans (bernstein_mono t L _ V hL ht
    (sum_nonneg fun i _ => mul_nonneg (hq i).1 (sq_nonneg _)) hV))
  congr 1
  funext ω
  apply propext
  constructor <;> intro h' <;> linarith

/-! ## Unweighted counts and their second factorial moment -/

/-- The number of retained coins in `J`, as a real number. -/
theorem card_filter_eq_lin (J : Finset (Fin n)) (ω : Fin n → Bool) :
    ((J.filter fun i => ω i = true).card : ℝ) = lin J (fun _ => 1) ω := by
  unfold lin
  rw [Finset.card_filter]
  push_cast
  rfl

theorem lin_one_sq (J : Finset (Fin n)) (ω : Fin n → Bool) :
    lin J (fun _ => 1) ω * (lin J (fun _ => 1) ω - 1) =
      ∑ i ∈ J, (if ω i then (1 : ℝ) else 0) * lin (J.erase i) (fun _ => 1) ω := by
  unfold lin
  rw [mul_sub, mul_one, sum_mul]
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro i hi
  rw [← add_sum_erase J _ hi]
  split_ifs <;> ring

/-- `E[D(D-1)] ≤ (E D)²` for a count of independent coins. -/
theorem cubeMean_count_pairs_le (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (J : Finset (Fin n)) :
    cubeMean q (fun ω => lin J (fun _ => 1) ω * (lin J (fun _ => 1) ω - 1)) ≤
      (∑ i ∈ J, q i) ^ 2 := by
  rw [cubeMean_congr q (lin_one_sq J), cubeMean_sum]
  rw [sum_congr rfl (fun i hi => cubeMean_coord_mul q i _
    (lin_indepOf _ _ _ (by simp)))]
  simp only [cubeMean_lin, mul_one]
  rw [sq, sum_mul]
  apply sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (hq i).1
  exact sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun j _ _ => (hq j).1)

end PartitionedTriangleAbsorption.Nibble
