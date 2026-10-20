/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Tactic

/-! # A uniform, rounded hierarchy for the request-wise cleanup

The parameters are chosen before the graph. The numerical budget includes
all internal requests and the full triangle-packing degree, not only its
new cross edges. No square-root estimates or graph-specific parameters are
assumed in the final existence theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupHierarchyStage140

noncomputable def defect (ε : ℝ) (n : ℕ) : ℕ := ⌊ε * n⌋₊
noncomputable def quota (a : ℝ) (n : ℕ) : ℕ := ⌈a * n⌉₊
noncomputable def supply (ε : ℝ) (n : ℕ) : ℕ := ⌊(1 / 4 - 11 * ε) * n⌋₊

/-- The real-valued budget underlying the rounded construction. -/
theorem real_budget (a n d q b m : ℝ)
    (ha : 0 < a) (ha1 : a ≤ 1 / 100) (hn : 0 < n)
    (hd : d ≤ a ^ 2 * n / 100)
    (hq : a * n ≤ q) (hq2 : q ≤ 2 * (a * n))
    (hb : n / 5 ≤ b) (hm : m ≤ n * d) :
    2 * m + 2 * (d + 2 * q) * q < b * q ∧
      2 * d + 2 * q ≤ 5 * (a * n) := by
  have hA : 0 < a * n := mul_pos ha hn
  have haq : 0 ≤ q := le_trans hA.le hq
  have haone : a ≤ 1 := by linarith
  have hdaa : a ^ 2 ≤ a := by nlinarith
  have hdA : d ≤ a * n / 100 := by
    have hp := mul_le_mul_of_nonneg_right hdaa hn.le
    linarith
  have hmA : m ≤ (a * n) ^ 2 / 100 := calc
    m ≤ n * d := hm
    _ ≤ n * (a ^ 2 * n / 100) := mul_le_mul_of_nonneg_left hd hn.le
    _ = (a * n) ^ 2 / 100 := by ring
  have hfactor : d + 2 * q ≤ a * n / 100 + 4 * (a * n) := by linarith
  have hprod : 2 * (d + 2 * q) * q ≤ (401 / 25 : ℝ) * (a * n) ^ 2 := calc
    2 * (d + 2 * q) * q ≤
        (2 * (a * n / 100 + 4 * (a * n))) * (2 * (a * n)) :=
      mul_le_mul (by linarith) hq2 haq (by positivity)
    _ = (401 / 25 : ℝ) * (a * n) ^ 2 := by ring
  have hleft : 2 * m + 2 * (d + 2 * q) * q ≤ 17 * (a * n) ^ 2 := by
    nlinarith only [hmA, hprod, sq_nonneg (a * n)]
  have hsmall : 17 * a < 1 / 5 := by linarith
  have hgap : 17 * (a * n) ^ 2 < n / 5 * (a * n) := by
    have ht := mul_lt_mul_of_pos_right hsmall (mul_pos ha (sq_pos_of_pos hn))
    nlinarith only [ht]
  have hright : n / 5 * (a * n) ≤ b * q :=
    mul_le_mul hb hq hA.le (by linarith)
  exact ⟨lt_of_le_of_lt hleft (lt_of_lt_of_le hgap hright), by linarith⟩

/-- All floor/ceiling errors are paid at a single graph-independent scale. -/
theorem rounded_budget (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1 / 100)
    (n : ℕ) (hn100 : (100 : ℝ) ≤ n) (hnscale : 1 ≤ a * n) :
    let ε := a ^ 2 / 100
    0 < n ∧ 0 < quota a n ∧
      (2 * defect ε n + 2 * quota a n : ℝ) ≤ 5 * (a * n) ∧
      ∀ m : ℕ, m ≤ n * defect ε n →
        2 * m + 2 * (defect ε n + 2 * quota a n) * quota a n <
          supply ε n * quota a n := by
  dsimp only
  have hn : (0 : ℝ) < n := by linarith
  have heps0 : 0 ≤ a ^ 2 / 100 := by positivity
  have heps : a ^ 2 / 100 ≤ (1 / 1000 : ℝ) := by nlinarith
  have hd : (defect (a ^ 2 / 100) n : ℝ) ≤ a ^ 2 * n / 100 := by
    have hh := Nat.floor_le (mul_nonneg heps0 hn.le)
    change (defect (a ^ 2 / 100) n : ℝ) ≤ _ at hh
    nlinarith only [hh]
  have hq := Nat.le_ceil (a * (n : ℝ))
  have hq2 : (quota a n : ℝ) ≤ 2 * (a * n) := by
    have hh := Nat.ceil_lt_add_one (mul_nonneg ha.le hn.le)
    change (quota a n : ℝ) < _ at hh
    linarith
  have hb : (n : ℝ) / 5 ≤ supply (a ^ 2 / 100) n := by
    have hh := Nat.lt_floor_add_one ((1 / 4 - 11 * (a ^ 2 / 100)) * (n : ℝ))
    change (1 / 4 - 11 * (a ^ 2 / 100)) * (n : ℝ) <
      (supply (a ^ 2 / 100) n : ℝ) + 1 at hh
    have hp := mul_le_mul_of_nonneg_right heps hn.le
    nlinarith only [hh, hp, hn100]
  have hquota : 0 < quota a n := by
    have : (0 : ℝ) < quota a n := lt_of_lt_of_le (mul_pos ha hn) hq
    exact_mod_cast this
  have hall : ∀ m : ℕ, m ≤ n * defect (a ^ 2 / 100) n →
      2 * m + 2 * (defect (a ^ 2 / 100) n + 2 * quota a n) * quota a n <
        supply (a ^ 2 / 100) n * quota a n := by
    intro m hm
    have hmR : (m : ℝ) ≤ n * (defect (a ^ 2 / 100) n : ℝ) := by exact_mod_cast hm
    have h := (real_budget a n (defect (a ^ 2 / 100) n) (quota a n)
      (supply (a ^ 2 / 100) n) m ha ha1 hn hd hq hq2 hb hmR).1
    exact_mod_cast h
  have hdegree := (real_budget a n (defect (a ^ 2 / 100) n) (quota a n)
    (supply (a ^ 2 / 100) n) 0 ha ha1 hn hd hq hq2 hb
    (by positivity)).2
  exact ⟨by exact_mod_cast hn, hquota, hdegree, hall⟩

/-- Uniform cleanup parameters determined solely by the permitted output loss. -/
theorem exists_hierarchy (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 1000 ∧
      ∃ a : ℝ, 0 < a ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        0 < n ∧ 0 < quota a n ∧
        (2 * defect ε n + 2 * quota a n : ℝ) ≤ η * n ∧
        ∀ m : ℕ, m ≤ n * defect ε n →
          2 * m + 2 * (defect ε n + 2 * quota a n) * quota a n <
            supply ε n * quota a n := by
  let a : ℝ := min (1 / 100) (η / 16)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a ≤ 1 / 100 := min_le_left _ _
  have haη : a ≤ η / 16 := min_le_right _ _
  obtain ⟨N, hN⟩ := exists_nat_gt (max (100 : ℝ) (1 / a))
  refine ⟨a ^ 2 / 100, by positivity, by nlinarith, a, ha, N, ?_⟩
  intro n hn
  have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hn100 : (100 : ℝ) ≤ n := (le_max_left _ _).trans ((le_of_lt hN).trans hnn)
  have hscale : 1 ≤ a * n := by
    have hh : 1 / a ≤ (n : ℝ) := (le_max_right _ _).trans ((le_of_lt hN).trans hnn)
    have hh' := (div_le_iff₀ ha).mp hh
    simpa only [mul_comm] using hh'
  obtain ⟨hn0, hq0, hdeg, hbud⟩ := rounded_budget a ha ha1 n hn100 hscale
  refine ⟨hn0, hq0, hdeg.trans ?_, hbud⟩
  have he : 5 * a ≤ η := by linarith
  have hh := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  nlinarith only [hh]

end PartitionedTriangleAbsorption.CleanupHierarchyStage140
