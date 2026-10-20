/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Pair fluctuations for the explicit four-class fractional inverse

Finite means split an arbitrary pair demand into a constant, two vertex
fluctuations and a pair fluctuation with zero row and column sums. The last
component lifts to transversal triangles without changing any other edge
demand. These are identities for all finite class sizes, not sampled tests.
The whole physical F3 inverse and the deleted-host contraction are separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FractionalAveragingStage72

open Finset

variable {A B C D : Type*}

noncomputable def mean [Fintype A] (f : A → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card A

theorem mean_const [Fintype A] [Nonempty A] (x : ℝ) :
    mean (fun _ : A => x) = x := by
  have hn : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hn]

theorem mean_add [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a + g a) = mean f + mean g := by
  simp only [mean, sum_add_distrib, add_div]

theorem mean_sub [Fintype A] (f g : A → ℝ) :
    mean (fun a => f a - g a) = mean f - mean g := by
  simp only [mean, sum_sub_distrib, sub_div]

theorem mean_comm [Fintype A] [Fintype B] (f : A → B → ℝ) :
    mean (fun a => mean (f a)) = mean (fun b => mean (fun a => f a b)) := by
  simp only [mean, sum_div, div_div]
  rw [sum_comm, mul_comm (Fintype.card B : ℝ)]

theorem abs_mean_le [Fintype A] [Nonempty A] (f : A → ℝ) (z : ℝ)
    (hf : ∀ a, |f a| ≤ z) : |mean f| ≤ z := by
  have hn : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  rw [mean, abs_div, abs_of_pos hn, div_le_iff₀ hn]
  calc
    |∑ a, f a| ≤ ∑ a, |f a| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : A, z := sum_le_sum (fun a _ => hf a)
    _ = z * Fintype.card A := by simp [mul_comm]

noncomputable def grandMean [Fintype A] [Fintype B] (f : A → B → ℝ) : ℝ :=
  mean (fun a => mean (f a))

noncomputable def rowFluctuation [Fintype A] [Fintype B]
    (f : A → B → ℝ) (a : A) : ℝ := mean (f a) - grandMean f

noncomputable def colFluctuation [Fintype A] [Fintype B]
    (f : A → B → ℝ) (b : B) : ℝ := mean (fun a => f a b) - grandMean f

noncomputable def pairFluctuation [Fintype A] [Fintype B]
    (f : A → B → ℝ) (a : A) (b : B) : ℝ :=
  f a b - mean (f a) - mean (fun a => f a b) + grandMean f

theorem demand_split [Fintype A] [Fintype B] (f : A → B → ℝ) (a : A) (b : B) :
    f a b = grandMean f + rowFluctuation f a + colFluctuation f b +
      pairFluctuation f a b := by
  unfold rowFluctuation colFluctuation pairFluctuation
  ring

theorem pair_mean_row [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B → ℝ) (a : A) : mean (pairFluctuation f a) = 0 := by
  change mean (fun b => f a b - mean (f a) - mean (fun a => f a b) + grandMean f) = 0
  simp only [mean_add, mean_sub, mean_const]
  rw [← mean_comm]
  unfold grandMean
  ring

theorem pair_mean_col [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B → ℝ) (b : B) : mean (fun a => pairFluctuation f a b) = 0 := by
  simp only [pairFluctuation, mean_add, mean_sub, mean_const]
  unfold grandMean
  ring

theorem pair_sum_row [Fintype A] [Fintype B] [Nonempty B]
    (f : A → B → ℝ) (a : A) : ∑ b, pairFluctuation f a b = 0 := by
  have hh := pair_mean_row f a
  rw [mean, div_eq_zero_iff] at hh
  exact hh.resolve_right (by exact_mod_cast Fintype.card_ne_zero)

theorem pair_sum_col [Fintype A] [Fintype B] [Nonempty A]
    (f : A → B → ℝ) (b : B) : ∑ a, pairFluctuation f a b = 0 := by
  have hh := pair_mean_col f b
  rw [mean, div_eq_zero_iff] at hh
  exact hh.resolve_right (by exact_mod_cast Fintype.card_ne_zero)

theorem pair_abs_le [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → B → ℝ) (z : ℝ) (hf : ∀ a b, |f a b| ≤ z) (a : A) (b : B) :
    |pairFluctuation f a b| ≤ 4 * z := by
  have hr := abs_mean_le (f a) z (hf a)
  have hc := abs_mean_le (fun a => f a b) z (fun a => hf a b)
  have hg := abs_mean_le (fun a => mean (f a)) z (fun a => abs_mean_le (f a) z (hf a))
  change |f a b - mean (f a) - mean (fun a => f a b) + grandMean f| ≤ _
  have h1 := abs_add_le (f a b - mean (f a) - mean (fun a => f a b)) (grandMean f)
  have h2 : |f a b - mean (f a) - mean (fun a => f a b)| ≤
      |f a b - mean (f a)| + |mean (fun a => f a b)| := by
    simpa only [sub_eq_add_neg, abs_neg] using
      abs_add_le (f a b - mean (f a)) (-mean (fun a => f a b))
  have h3 : |f a b - mean (f a)| ≤ |f a b| + |mean (f a)| := by
    simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (f a b) (-mean (f a))
  change |grandMean f| ≤ z at hg
  linarith [hf a b]

/-- One pair fluctuation is split equally between the two remaining classes.
Its two opposite marginal loads vanish because its rows and columns sum to zero.
The product types label genuine triples in three distinct vertex classes. -/
theorem pair_lift_marginals [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [Nonempty C] [Nonempty D] (f : A → B → ℝ)
    (hrow : ∀ a, ∑ b, f a b = 0) (hcol : ∀ b, ∑ a, f a b = 0) :
    (∀ a b, (∑ _ : C, f a b / (2 * Fintype.card C)) +
      (∑ _ : D, f a b / (2 * Fintype.card D)) = f a b) ∧
    (∀ a, (∑ b, f a b / (2 * Fintype.card C)) = 0) ∧
    (∀ b, (∑ a, f a b / (2 * Fintype.card C)) = 0) ∧
    (∀ a, (∑ b, f a b / (2 * Fintype.card D)) = 0) ∧
    (∀ b, (∑ a, f a b / (2 * Fintype.card D)) = 0) := by
  have hC : (Fintype.card C : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD : (Fintype.card D : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b
    simp only [sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring
  · intro a
    rw [← sum_div, hrow, zero_div]
  · intro b
    rw [← sum_div, hcol, zero_div]
  · intro a
    rw [← sum_div, hrow, zero_div]
  · intro b
    rw [← sum_div, hcol, zero_div]

end PartitionedTriangleAbsorption.FractionalAveragingStage72
