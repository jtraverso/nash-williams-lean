/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.K5EdgeGadget
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Exact repair from a supplied finite edge kernel

The incidence matrix and its right inverse are explicit inputs. The existence
and load bound of a physical host kernel are not asserted by this consumer.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FinitePackingRepair

open Finset

variable {E T : Type*} [Fintype E] [Fintype T]

def mass (A : E → T → ℝ) (w : T → ℝ) (e : E) : ℝ :=
  ∑ t, A e t * w t

def repaired (A : E → T → ℝ) (K : E → T → ℝ) (w : T → ℝ) (t : T) : ℝ :=
  w t + ∑ e, (1 - mass A w e) * K e t

/-- A right inverse corrects every edge mass exactly, not merely on average. -/
theorem repaired_mass [DecidableEq E] (A K : E → T → ℝ) (w : T → ℝ)
    (hK : ∀ e f, (∑ t, A f t * K e t) = if e = f then 1 else 0) (f : E) :
    mass A (repaired A K w) f = 1 := by
  classical
  unfold mass repaired
  simp_rw [mul_add, mul_sum]
  rw [sum_add_distrib, sum_comm]
  have hs : (∑ e, ∑ t, A f t * ((1 - mass A w e) * K e t)) =
      1 - mass A w f := by
    simp_rw [show ∀ e t, A f t * ((1 - mass A w e) * K e t) =
      (1 - mass A w e) * (A f t * K e t) from fun e t => by ring]
    simp_rw [← mul_sum, hK]
    simp
  rw [hs]
  change mass A w f + (1 - mass A w f) = 1
  ring

/-- The coordinate cost is controlled by the absolute row load of the kernel. -/
theorem repair_bound (A K : E → T → ℝ) (w : T → ℝ) (δ L : ℝ)
    (hδ : 0 ≤ δ) (hm : ∀ e, 1 - δ ≤ mass A w e ∧ mass A w e ≤ 1)
    (hload : ∀ t, (∑ e, |K e t|) ≤ L) (t : T) :
    |repaired A K w t - w t| ≤ δ * L := by
  classical
  have hb : ∀ e, |1 - mass A w e| ≤ δ := by
    intro e
    rw [abs_of_nonneg (by linarith [(hm e).2])]
    linarith [(hm e).1]
  calc
    |repaired A K w t - w t| = |∑ e, (1 - mass A w e) * K e t| := by
      unfold repaired
      congr 1
      ring
    _ ≤ ∑ e, |(1 - mass A w e) * K e t| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, δ * |K e t| := by
      apply sum_le_sum
      intro e _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb e) (abs_nonneg _)
    _ = δ * ∑ e, |K e t| := (mul_sum _ _ _).symm
    _ ≤ δ * L := mul_le_mul_of_nonneg_left (hload t) hδ

/-- A repair costing at most half the lower seed stays positive and bounded. -/
theorem seeded_bounds (a b cost x y : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hx : a ≤ x ∧ x ≤ b) (hy : |y - x| ≤ cost) (hc : cost ≤ a / 2) :
    a / 2 ≤ y ∧ y ≤ 2 * b := by
  have hh := abs_le.mp hy
  constructor <;> linarith

/-- The output is an actual weight vector; all host construction obligations
remain visible in the right-inverse and absolute-load hypotheses. -/
theorem exists_positive_exact_repair [DecidableEq E]
    (A K : E → T → ℝ) (w : T → ℝ) (a b δ L : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hδ : 0 ≤ δ)
    (hw : ∀ t, a ≤ w t ∧ w t ≤ b)
    (hm : ∀ e, 1 - δ ≤ mass A w e ∧ mass A w e ≤ 1)
    (hK : ∀ e f, (∑ t, A f t * K e t) = if e = f then 1 else 0)
    (hload : ∀ t, (∑ e, |K e t|) ≤ L) (hc : δ * L ≤ a / 2) :
    ∃ w' : T → ℝ, (∀ e, mass A w' e = 1) ∧
      (∀ t, a / 2 ≤ w' t ∧ w' t ≤ 2 * b) := by
  refine ⟨repaired A K w, repaired_mass A K w hK, ?_⟩
  intro t
  exact seeded_bounds a b (δ * L) (w t) (repaired A K w t)
    ha.le hab (hw t) (repair_bound A K w δ L hδ hm hload t) hc

end PartitionedTriangleAbsorption.FinitePackingRepair
