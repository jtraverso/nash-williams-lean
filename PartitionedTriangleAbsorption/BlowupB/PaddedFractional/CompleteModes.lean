/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Exact signed corrections for the edge modes of a complete typed host

These formulas handle the residual after class totals and vertex-to-class
degrees have been corrected.  In the tripartite case the zero row and column
sums make both unwanted edge loads vanish.  When the completion repeats one
class, the denominator is `card A - 2`, rather than `card A - 1`: the second
copy of the repeated class contributes the missing negative row term.

The statements concern real signed weights.  They are not a positivity or a
post-deletion regularity theorem, and do not assert `KeevashPaddedSpec`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- A scalar payload extended uniformly in a new class has its original load. -/
theorem uniform_sum (x : ℝ) (hn : (Fintype.card C : ℝ) ≠ 0) :
    (∑ _c : C, x / (Fintype.card C : ℝ)) = x := by
  simp only [sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- All three edge loads for a triangle with three distinct classes. -/
theorem tripartite_edge_mode (g : A → B → ℝ)
    (hrow : ∀ a, ∑ b : B, g a b = 0)
    (hcol : ∀ b, ∑ a : A, g a b = 0)
    (hn : (Fintype.card C : ℝ) ≠ 0) :
    (∀ a b, (∑ _c : C, g a b / (Fintype.card C : ℝ)) = g a b) ∧
    (∀ a, (∑ b : B, g a b / (Fintype.card C : ℝ)) = 0) ∧
    (∀ b, (∑ a : A, g a b / (Fintype.card C : ℝ)) = 0) := by
  refine ⟨fun a b => uniform_sum (C := C) (g a b) hn, ?_, ?_⟩
  · intro a
    rw [← sum_div, hrow, zero_div]
  · intro b
    rw [← sum_div, hcol, zero_div]

/-- The exact numerator identity responsible for the `card A - 2` correction. -/
theorem repeated_numerator [DecidableEq A] (f : A → ℝ)
    (hf : ∑ a : A, f a = 0) (a : A) :
    (∑ a' ∈ univ.erase a, (f a + f a')) =
      ((Fintype.card A : ℝ) - 2) * f a := by
  have h := sum_erase_add univ (fun a' => f a + f a') (mem_univ a)
  have htotal : (∑ a' : A, (f a + f a')) = (Fintype.card A : ℝ) * f a := by
    rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, hf, add_zero]
  rw [htotal] at h
  linarith

omit [Fintype B] in
/-- The load on the two cross-class edges of a repeated-class triangle. -/
theorem repeated_cross_load [DecidableEq A] (g : A → B → ℝ)
    (hcol : ∀ b, ∑ a : A, g a b = 0)
    (hn : (Fintype.card A : ℝ) - 2 ≠ 0) (a : A) (b : B) :
    (∑ a' ∈ univ.erase a,
      (g a b + g a' b) / ((Fintype.card A : ℝ) - 2)) = g a b := by
  rw [← sum_div, repeated_numerator (fun a => g a b) (hcol b) a]
  exact mul_div_cancel_left₀ _ hn

/-- The unwanted internal edge load vanishes by the two zero row sums. -/
theorem repeated_internal_load (g : A → B → ℝ)
    (hrow : ∀ a, ∑ b : B, g a b = 0) (a a' : A) :
    (∑ b : B, (g a b + g a' b) / ((Fintype.card A : ℝ) - 2)) = 0 := by
  rw [← sum_div, sum_add_distrib, hrow, hrow, add_zero, zero_div]

/-- Both edge modes for a triangle whose first two vertices have the same class. -/
theorem repeated_edge_mode [DecidableEq A] (g : A → B → ℝ)
    (hrow : ∀ a, ∑ b : B, g a b = 0)
    (hcol : ∀ b, ∑ a : A, g a b = 0)
    (hn : (Fintype.card A : ℝ) - 2 ≠ 0) :
    (∀ a b, (∑ a' ∈ univ.erase a,
      (g a b + g a' b) / ((Fintype.card A : ℝ) - 2)) = g a b) ∧
    (∀ a a', (∑ b : B,
      (g a b + g a' b) / ((Fintype.card A : ℝ) - 2)) = 0) :=
  ⟨repeated_cross_load g hcol hn, repeated_internal_load g hrow⟩

/-- A zero-diagonal zero-row internal payload has zero sum away from its diagonal. -/
theorem internal_erase_sum [DecidableEq A] (g : A → A → ℝ)
    (hrow : ∀ a, ∑ a' : A, g a a' = 0) (hdiag : ∀ a, g a a = 0) (a : A) :
    (∑ a' ∈ univ.erase a, g a a') = 0 := by
  have h := sum_erase_add univ (fun a' => g a a') (mem_univ a)
  rw [hrow, hdiag, add_zero] at h
  exact h

/-- Correcting an internal edge uniformly in another class creates no cross load. -/
theorem internal_edge_mode [DecidableEq A] (g : A → A → ℝ)
    (hrow : ∀ a, ∑ a' : A, g a a' = 0) (hdiag : ∀ a, g a a = 0)
    (hn : (Fintype.card B : ℝ) ≠ 0) :
    (∀ a a', (∑ _b : B, g a a' / (Fintype.card B : ℝ)) = g a a') ∧
    (∀ a, (∑ a' ∈ univ.erase a, g a a' / (Fintype.card B : ℝ)) = 0) := by
  refine ⟨fun a a' => uniform_sum (C := B) (g a a') hn, ?_⟩
  intro a
  rw [← sum_div, internal_erase_sum g hrow hdiag a, zero_div]

/-- Uniform completion preserves the expected coefficient bound. -/
theorem uniform_bound (x ε d : ℝ) (hx : |x| ≤ ε) (hd : 0 < d) :
    |x / d| ≤ ε / d := by
  rw [abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hx hd.le

/-- The repeated-class mode costs a factor of at most two in its numerator. -/
theorem repeated_bound (x y ε d : ℝ)
    (hx : |x| ≤ ε) (hy : |y| ≤ ε) (hd : 0 < d) :
    |(x + y) / d| ≤ 2 * ε / d := by
  apply uniform_bound (x + y) (2 * ε) d ?_ hd
  exact (abs_add_le x y).trans (by linarith)

/-- Repeated-class vertex corrections give the same specified degree in both classes. -/
theorem repeated_vertex_mode [DecidableEq A] (f : A → ℝ)
    (hf : ∑ a : A, f a = 0)
    (hA : (Fintype.card A : ℝ) - 2 ≠ 0)
    (hB : (Fintype.card B : ℝ) ≠ 0) :
    (∀ a, (∑ a' ∈ univ.erase a, ∑ _b : B,
      (f a + f a') /
        (((Fintype.card A : ℝ) - 2) * (Fintype.card B : ℝ))) = f a) ∧
    (∀ a, (∑ _b : B, ∑ a' ∈ univ.erase a,
      (f a + f a') /
        (((Fintype.card A : ℝ) - 2) * (Fintype.card B : ℝ))) = f a) ∧
    ((∑ a : A, f a / (Fintype.card B : ℝ)) = 0) := by
  have hfirst : ∀ a, (∑ a' ∈ univ.erase a, ∑ _b : B,
      (f a + f a') /
        (((Fintype.card A : ℝ) - 2) * (Fintype.card B : ℝ))) = f a := by
    intro a
    simp only [div_mul_eq_div_div]
    simp_rw [uniform_sum (C := B) _ hB]
    rw [← sum_div, repeated_numerator f hf a]
    exact mul_div_cancel_left₀ _ hA
  refine ⟨hfirst, ?_, ?_⟩
  · intro a
    rw [sum_comm]
    exact hfirst a
  · rw [← sum_div, hf, zero_div]

#print axioms tripartite_edge_mode
#print axioms repeated_edge_mode
#print axioms internal_edge_mode
#print axioms uniform_bound
#print axioms repeated_bound
#print axioms repeated_vertex_mode

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
