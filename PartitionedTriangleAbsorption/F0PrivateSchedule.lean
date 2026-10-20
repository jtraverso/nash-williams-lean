/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompressedHierarchyBudget

/-! # Pay the refiner and private-family budgets from one host-independent scale. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0PrivateSchedule

/-- The two rounded linear quotas pay a quadratic library and the final degree. -/
theorem exists_schedule (β η : ℝ) (hβ : 0 < β) (hη : 0 < η) (b : ℕ) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ M q : ℕ, 0 < q ∧ 2 * q ≤ n ∧ μ * n ≤ M ∧
        (b : ℝ) * (μ ^ 2 * (n : ℝ) ^ 2) ≤ (q : ℝ) * q ∧
        (q : ℝ) + 6 * (3 * μ * n + b * (M + q)) ≤ β * n / 2 ∧
        μ * n + b * (M + q) ≤ η * n := by
  let τ := min (1 / 8 : ℝ) (min (η / (100 * (b + 1))) (β / (100 * (b + 1))))
  let μ := τ / (100 * (b + 1))
  have hb : (0 : ℝ) < b + 1 := by positivity
  have ht : 0 < τ := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have ht8 : τ ≤ 1 / 8 := min_le_left _ _
  have htη : 100 * (b + 1 : ℝ) * τ ≤ η := by
    have h : τ ≤ η / (100 * (b + 1 : ℝ)) :=
      (min_le_right _ _).trans (min_le_left _ _)
    nlinarith only [(le_div_iff₀ (by positivity)).mp h]
  have htβ : 100 * (b + 1 : ℝ) * τ ≤ β := by
    have h : τ ≤ β / (100 * (b + 1 : ℝ)) :=
      (min_le_right _ _).trans (min_le_right _ _)
    nlinarith only [(le_div_iff₀ (by positivity)).mp h]
  have hm : 0 < μ := by dsimp [μ]; positivity
  have hmeq : 100 * (b + 1 : ℝ) * μ = τ := by
    dsimp [μ]
    field_simp
  have hmt : μ ≤ τ := by
    nlinarith only [hmeq, hm.le, (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hbmt : (b : ℝ) * μ ≤ τ := by
    nlinarith only [hmeq, hm.le, mul_nonneg (Nat.cast_nonneg b) hm.le]
  have hm2 : (b : ℝ) * μ ^ 2 ≤ τ ^ 2 := by
    have h := mul_le_mul hbmt hmt hm.le ht.le
    nlinarith only [h]
  have hfinal : (1 + 4 * (b : ℝ)) * τ ≤ η := by
    nlinarith only [htη, ht.le, mul_nonneg (Nat.cast_nonneg b) ht.le]
  have hgeom : (20 + 24 * (b : ℝ)) * τ ≤ β / 2 := by
    nlinarith only [htβ, ht.le, mul_nonneg (Nat.cast_nonneg b) ht.le]
  obtain ⟨N, hN⟩ := exists_nat_gt (max (1 / μ) (1 / τ))
  refine ⟨μ, hm, N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hmn : 1 ≤ μ * n := by
    have h := lt_of_lt_of_le ((le_max_left _ _).trans_lt hN) hNn
    have := (div_lt_iff₀ hm).mp h
    linarith only [this]
  have htn : 1 ≤ τ * n := by
    have h := lt_of_lt_of_le ((le_max_right _ _).trans_lt hN) hNn
    have := (div_lt_iff₀ ht).mp h
    linarith only [this]
  have hnpos : (0 : ℝ) < n := by nlinarith only [hm, hmn]
  let M := ⌈μ * n⌉₊
  let q := ⌈τ * n⌉₊
  have hMlo : μ * n ≤ (M : ℝ) := Nat.le_ceil _
  have hqlo : τ * n ≤ (q : ℝ) := Nat.le_ceil _
  have hMhi : (M : ℝ) ≤ 2 * μ * n := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hm.le hnpos.le)
    change (M : ℝ) < μ * n + 1 at h
    linarith only [h, hmn]
  have hqhi : (q : ℝ) ≤ 2 * τ * n := by
    have h := Nat.ceil_lt_add_one (mul_nonneg ht.le hnpos.le)
    change (q : ℝ) < τ * n + 1 at h
    linarith only [h, htn]
  have hqpos : 0 < q := Nat.ceil_pos.mpr (mul_pos ht hnpos)
  have hqn : 2 * q ≤ n := by
    have h := mul_le_mul_of_nonneg_right ht8 hnpos.le
    have h' : (2 * q : ℝ) ≤ n := by linarith only [h, hqhi, hnpos.le]
    exact_mod_cast h'
  have hmass : (b : ℝ) * (μ ^ 2 * (n : ℝ) ^ 2) ≤ (q : ℝ) * q := by
    have h := mul_le_mul_of_nonneg_right hm2 (sq_nonneg (n : ℝ))
    have h' := pow_le_pow_left₀ (mul_nonneg ht.le hnpos.le) hqlo 2
    nlinarith only [h, h']
  have hMτ : (M : ℝ) ≤ 2 * τ * n := hMhi.trans
    (by nlinarith only [mul_le_mul_of_nonneg_right hmt hnpos.le])
  have hgeomn := mul_le_mul_of_nonneg_right hgeom hnpos.le
  have hfinaln := mul_le_mul_of_nonneg_right hfinal hnpos.le
  have hμn := mul_le_mul_of_nonneg_right hmt hnpos.le
  have hpieces := mul_le_mul_of_nonneg_left (add_le_add hMτ hqhi)
    (Nat.cast_nonneg b : (0 : ℝ) ≤ b)
  refine ⟨M, q, hqpos, hqn, hMlo, hmass, ?_, ?_⟩
  · nlinarith only [hqhi, hμn, hpieces, hgeomn]
  · nlinarith only [hμn, hpieces, hfinaln]

end PartitionedTriangleAbsorption.F0PrivateSchedule
