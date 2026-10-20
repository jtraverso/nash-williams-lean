/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.SignlessBounds

@[expose] public section

/-!
# Support and global-order form of the physical signless inverse

The inverse uses only actual graph edges. The final estimate permits a global
order `n` larger than the order of the internal part on which it is constructed.
-/

namespace PartitionedTriangleAbsorption.F0Direct.SignlessTriangle

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem pivot_eq_zero_of_not_mem (G : SimpleGraph V)
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w)
    {e : Sym2 V} (he : e ∉ G.edgeSet) : pivot u v w e = 0 := by
  classical
  have hne (a b : V) (hab : G.Adj a b) : e ≠ s(a, b) := by
    intro heq
    apply he
    rw [heq]
    exact hab
  simp [pivot, edgeUnit, hne u v huv, hne u w huw, hne v w hvw]

theorem averagedPivot_eq_zero_of_not_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) {e : Sym2 V} (he : e ∉ G.edgeSet) : averagedPivot G u e = 0 := by
  classical
  have hterm : ∀ vw ∈ trianglePairs G u, pivot u vw.1 vw.2 e = 0 := by
    intro vw hvw
    obtain ⟨huv, huw, hvw⟩ := (mem_filter.mp hvw).2
    exact pivot_eq_zero_of_not_mem G huv huw hvw he
  simp only [averagedPivot, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_eq_zero hterm, mul_zero]

theorem triangleInverse_eq_zero_of_not_mem (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V → ℝ) {e : Sym2 V} (he : e ∉ G.edgeSet) : triangleInverse G x e = 0 := by
  classical
  simp only [triangleInverse, LinearMap.sum_apply, Finset.sum_apply,
    LinearMap.smulRight_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
    averagedPivot_eq_zero_of_not_mem G _ he, mul_zero, Finset.sum_const_zero]

/-- The coefficient bound in terms of the order of the full two-part host.
The lower bound counts ordered opposite pairs, so `2*tau*n^2` corresponds
to at least `tau*n^2` unordered triangles through each vertex. -/
theorem triangleInverse_abs_le_global_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n tau M : ℝ) (hn : 0 < n) (htau : 0 < tau) (hM : 0 ≤ M)
    (hcard : (Fintype.card V : ℝ) ≤ n)
    (hcount : ∀ u, 2 * tau * n ^ 2 ≤ ((trianglePairs G u).card : ℝ))
    (x : V → ℝ) (hx : ∀ u, |x u| ≤ M) (e : Sym2 V) :
    |triangleInverse G x e| ≤ 3 * M / (2 * tau * n) := by
  have hden : 0 < 2 * tau * n ^ 2 := by positivity
  calc
    _ ≤ 3 * (Fintype.card V : ℝ) * M / (2 * tau * n ^ 2) :=
      triangleInverse_abs_le G (2 * tau * n ^ 2) M hden hM hcount x hx e
    _ ≤ 3 * n * M / (2 * tau * n ^ 2) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) hM
    _ = 3 * M / (2 * tau * n) := by
      field_simp

/-- Actual triangle abundance supplies both exactness and support of the same
linear inverse, with a bound stated at the global order of the host. -/
theorem triangleInverse_spec_global_order
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (n tau : ℝ) (hn : 0 < n) (htau : 0 < tau)
    (hcard : (Fintype.card V : ℝ) ≤ n)
    (hcount : ∀ u, 2 * tau * n ^ 2 ≤ ((trianglePairs G u).card : ℝ)) :
    (∀ x, incidence G (triangleInverse G x) = x) ∧
    (∀ x e, e ∉ G.edgeSet → triangleInverse G x e = 0) ∧
    (∀ (x : V → ℝ) (M : ℝ), 0 ≤ M → (∀ u, |x u| ≤ M) →
      ∀ e, |triangleInverse G x e| ≤ 3 * M / (2 * tau * n)) := by
  have hpos (u : V) : 0 < (trianglePairs G u).card := by
    have : (0 : ℝ) < ((trianglePairs G u).card : ℝ) :=
      lt_of_lt_of_le (by positivity) (hcount u)
    exact_mod_cast this
  refine ⟨incidence_triangleInverse G hpos, ?_, ?_⟩
  · intro x e he
    exact triangleInverse_eq_zero_of_not_mem G x he
  · intro x M hM hx e
    exact triangleInverse_abs_le_global_order G n tau M hn htau hM hcard hcount x hx e

#print axioms triangleInverse_eq_zero_of_not_mem
#print axioms triangleInverse_spec_global_order

end PartitionedTriangleAbsorption.F0Direct.SignlessTriangle
