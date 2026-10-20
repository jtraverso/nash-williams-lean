/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.SignlessTriangle
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Physical coefficient bounds for the triangle incidence inverse

An edge belongs to at most six rooted ordered triangle positions per possible
third vertex. This module proves that counting bound and uses it to control
the explicit signless inverse. No sampling or asymptotic inference is used.
-/

namespace PartitionedTriangleAbsorption.F0Direct.SignlessTriangle

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem edgeUnit_nonneg (e f : Sym2 V) : 0 ≤ edgeUnit e f := by
  classical
  simp only [edgeUnit, Pi.single_apply]
  split_ifs <;> norm_num

omit [Fintype V] in
theorem abs_edgeUnit (e f : Sym2 V) : |edgeUnit e f| = edgeUnit e f :=
  abs_of_nonneg (edgeUnit_nonneg e f)

theorem abs_pivot_le (u v w : V) (e : Sym2 V) :
    |pivot u v w e| ≤ edgeUnit s(u, v) e + edgeUnit s(u, w) e + edgeUnit s(v, w) e := by
  change |edgeUnit s(u, v) e + edgeUnit s(u, w) e - edgeUnit s(v, w) e| ≤ _
  calc
    _ ≤ |edgeUnit s(u, v) e + edgeUnit s(u, w) e| + |edgeUnit s(v, w) e| :=
      by simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (edgeUnit s(u, v) e + edgeUnit s(u, w) e) (-edgeUnit s(v, w) e)
    _ ≤ |edgeUnit s(u, v) e| + |edgeUnit s(u, w) e| + |edgeUnit s(v, w) e| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ = _ := by simp only [abs_edgeUnit]

/-- An unordered physical edge has at most two ordered representations. -/
theorem sum_edgeUnit_le_two (e : Sym2 V) :
    (∑ u : V, ∑ v : V, edgeUnit s(u, v) e) ≤ 2 := by
  classical
  induction e using Sym2.ind with
  | _ a b =>
    have hpoint (u v : V) : edgeUnit s(u, v) s(a, b) ≤
        (if u = a ∧ v = b then (1 : ℝ) else 0) +
        (if u = b ∧ v = a then (1 : ℝ) else 0) := by
      by_cases heq : s(u, v) = s(a, b)
      · have hunit : edgeUnit s(u, v) s(a, b) = 1 := by
          rw [heq]
          simp [edgeUnit]
        rw [hunit]
        rcases Sym2.eq_iff.mp heq with h1 | h2
        · rw [if_pos h1]
          split_ifs <;> norm_num
        · rw [if_pos h2]
          split_ifs <;> norm_num
      · have hunit : edgeUnit s(u, v) s(a, b) = 0 := by
          simp [edgeUnit, heq, Ne.symm heq]
        rw [hunit]
        positivity
    calc
      _ ≤ ∑ u : V, ∑ v : V,
          ((if u = a ∧ v = b then (1 : ℝ) else 0) +
           (if u = b ∧ v = a then (1 : ℝ) else 0)) :=
        sum_le_sum fun u _ => sum_le_sum fun v _ => hpoint u v
      _ = 2 := by norm_num [Finset.sum_add_distrib, ite_and]

/-- Total absolute pivot incidence at a fixed physical edge. -/
theorem sum_abs_pivot_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) :
    (∑ u : V, ∑ vw ∈ trianglePairs G u, |pivot u vw.1 vw.2 e|) ≤
      6 * (Fintype.card V : ℝ) := by
  classical
  let majorant (u : V) (vw : V × V) : ℝ :=
    edgeUnit s(u, vw.1) e + edgeUnit s(u, vw.2) e + edgeUnit s(vw.1, vw.2) e
  have hnonneg (u : V) (vw : V × V) : 0 ≤ majorant u vw :=
    add_nonneg (add_nonneg (edgeUnit_nonneg _ _) (edgeUnit_nonneg _ _))
      (edgeUnit_nonneg _ _)
  have hsub : (∑ u : V, ∑ vw ∈ trianglePairs G u, |pivot u vw.1 vw.2 e|) ≤
      ∑ u : V, ∑ vw : V × V, majorant u vw := by
    apply sum_le_sum
    intro u _
    calc
      _ ≤ ∑ vw ∈ trianglePairs G u, majorant u vw :=
        sum_le_sum fun vw _ => abs_pivot_le u vw.1 vw.2 e
      _ ≤ ∑ vw : V × V, majorant u vw :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun vw _ _ => hnonneg u vw)
  let P : ℝ := ∑ u : V, ∑ v : V, edgeUnit s(u, v) e
  let n : ℝ := Fintype.card V
  have hfirst : (∑ u : V, ∑ v : V, ∑ _w : V, edgeUnit s(u, v) e) = n * P := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rfl
  have hsecond : (∑ u : V, ∑ _v : V, ∑ w : V, edgeUnit s(u, w) e) = n * P := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum]
    rfl
  have hthird : (∑ _u : V, ∑ v : V, ∑ w : V, edgeUnit s(v, w) e) = n * P := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  have hfull : (∑ u : V, ∑ vw : V × V, majorant u vw) = 3 * n * P := by
    simp only [majorant, Fintype.sum_prod_type, Finset.sum_add_distrib]
    rw [hfirst, hsecond, hthird]
    ring
  have hP : P ≤ 2 := sum_edgeUnit_le_two e
  have hn : 0 ≤ n := Nat.cast_nonneg _
  calc
    _ ≤ ∑ u : V, ∑ vw : V × V, majorant u vw := hsub
    _ = 3 * n * P := hfull
    _ ≤ 6 * n := by nlinarith

/-- A lower bound `d` on ordered triangle counts gives a uniform physical
coefficient bound for the explicit signless inverse. With
`d = 2*tau*n^2`, this is `3 M / (2*tau*n)`. -/
theorem triangleInverse_abs_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (d M : ℝ) (hd : 0 < d) (hM : 0 ≤ M)
    (hcount : ∀ u, d ≤ ((trianglePairs G u).card : ℝ))
    (x : V → ℝ) (hx : ∀ u, |x u| ≤ M) (e : Sym2 V) :
    |triangleInverse G x e| ≤ 3 * (Fintype.card V : ℝ) * M / d := by
  classical
  let c : ℝ := M / (2 * d)
  have hc : 0 ≤ c := div_nonneg hM (by positivity)
  have hcoef (u : V) : |x u * (2 * ((trianglePairs G u).card : ℝ))⁻¹| ≤ c := by
    have hden : 0 < 2 * ((trianglePairs G u).card : ℝ) := by nlinarith [hcount u]
    rw [← div_eq_mul_inv, abs_div, abs_of_pos hden]
    calc
      _ ≤ M / (2 * ((trianglePairs G u).card : ℝ)) :=
        div_le_div_of_nonneg_right (hx u) hden.le
      _ ≤ M / (2 * d) :=
        div_le_div_of_nonneg_left hM (by positivity) (by linarith [hcount u])
  have hform : triangleInverse G x e = ∑ u : V, ∑ vw ∈ trianglePairs G u,
      (x u * (2 * ((trianglePairs G u).card : ℝ))⁻¹) * pivot u vw.1 vw.2 e := by
    simp only [triangleInverse, LinearMap.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply, averagedPivot, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [Finset.mul_sum, mul_assoc]
  rw [hform]
  calc
    _ ≤ ∑ u : V, |∑ vw ∈ trianglePairs G u,
        (x u * (2 * ((trianglePairs G u).card : ℝ))⁻¹) * pivot u vw.1 vw.2 e| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ u : V, ∑ vw ∈ trianglePairs G u,
        |(x u * (2 * ((trianglePairs G u).card : ℝ))⁻¹) * pivot u vw.1 vw.2 e| :=
      sum_le_sum fun u _ => abs_sum_le_sum_abs _ _
    _ ≤ ∑ u : V, ∑ vw ∈ trianglePairs G u, c * |pivot u vw.1 vw.2 e| := by
      apply sum_le_sum
      intro u _
      apply sum_le_sum
      intro vw _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hcoef u) (abs_nonneg _)
    _ = c * (∑ u : V, ∑ vw ∈ trianglePairs G u, |pivot u vw.1 vw.2 e|) := by
      simp only [Finset.mul_sum]
    _ ≤ c * (6 * (Fintype.card V : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_abs_pivot_le G e) hc
    _ = 3 * (Fintype.card V : ℝ) * M / d := by
      dsimp [c]
      ring

#print axioms sum_abs_pivot_le
#print axioms triangleInverse_abs_le

end PartitionedTriangleAbsorption.F0Direct.SignlessTriangle
