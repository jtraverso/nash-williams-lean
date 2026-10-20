/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# A signless incidence inverse obtained by averaging triangle pivots

For a triangle on `u,v,w`, the edge vector `uv + uw - vw` has signless
incidence `2` at `u` and `0` elsewhere. Averaging these pivots over every
triangle through `u`, then summing over `u`, gives a linear right inverse
whenever every vertex lies in an internal triangle.

This module establishes the exact algebraic identity. Its hypothesis is
positivity of the actual triangle count, not a right-inverse assumption.
-/

namespace PartitionedTriangleAbsorption.F0Direct.SignlessTriangle

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def incidence (G : SimpleGraph V) [DecidableRel G.Adj] :
    (Sym2 V → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun x u := ∑ e : Sym2 V, G.incMatrix ℝ u e * x e
  map_add' x y := by
    funext u
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    ring

noncomputable def edgeUnit (e : Sym2 V) : Sym2 V → ℝ := Pi.single e 1

theorem incidence_edgeUnit (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Sym2 V) (z : V) :
    incidence G (edgeUnit e) z = G.incMatrix ℝ z e := by
  classical
  simp [incidence, edgeUnit, Pi.single_apply, mul_ite]

noncomputable def pivot (u v w : V) : Sym2 V → ℝ :=
  edgeUnit s(u, v) + edgeUnit s(u, w) - edgeUnit s(v, w)

/-- The elementary triangle pivot, at the level of physical unordered edges. -/
theorem incidence_pivot (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v w : V} (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) :
    incidence G (pivot u v w) = (2 : ℝ) • Pi.single u 1 := by
  classical
  have huv' := G.ne_of_adj huv
  have huw' := G.ne_of_adj huw
  have hvw' := G.ne_of_adj hvw
  funext z
  simp only [pivot, map_sub, map_add, Pi.sub_apply, Pi.add_apply,
    incidence_edgeUnit, Pi.smul_apply, smul_eq_mul]
  by_cases hzu : z = u
  · subst z
    norm_num [SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff,
      huv, huw, hvw, huv', huw']
  · by_cases hzv : z = v
    · subst z
      simp [SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff,
        huv, huw, hvw, huv'.symm, hvw']
    · by_cases hzw : z = w
      · subst z
        simp [SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff,
          huv, huw, hvw, huw'.symm, hvw'.symm]
      · simp [SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff,
          huv, huw, hvw, hzu, hzv, hzw]

/-- Ordered opposite pairs in triangles rooted at `u`; every unordered triangle
through `u` contributes exactly two pairs. -/
def trianglePairs (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset (V × V) :=
  univ.filter fun vw => G.Adj u vw.1 ∧ G.Adj u vw.2 ∧ G.Adj vw.1 vw.2

noncomputable def averagedPivot (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    Sym2 V → ℝ :=
  (2 * ((trianglePairs G u).card : ℝ))⁻¹ •
    ∑ vw ∈ trianglePairs G u, pivot u vw.1 vw.2

theorem incidence_averagedPivot (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (hpos : 0 < (trianglePairs G u).card) :
    incidence G (averagedPivot G u) = Pi.single u 1 := by
  classical
  have hn : ((trianglePairs G u).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have heach : ∀ vw ∈ trianglePairs G u,
      incidence G (pivot u vw.1 vw.2) = (2 : ℝ) • Pi.single u 1 := by
    intro vw hvw
    obtain ⟨huv, huw, hvw⟩ := (mem_filter.mp hvw).2
    exact incidence_pivot G huv huw hvw
  rw [averagedPivot, map_smul, map_sum]
  have hsum : (∑ vw ∈ trianglePairs G u, incidence G (pivot u vw.1 vw.2)) =
      ∑ _vw ∈ trianglePairs G u, (2 : ℝ) • Pi.single u 1 :=
    Finset.sum_congr rfl heach
  rw [hsum]
  funext z
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
  rw [Finset.sum_const, nsmul_eq_mul]
  field_simp [hn]

/-- The explicit linear incidence inverse obtained by averaging actual triangles. -/
noncomputable def triangleInverse (G : SimpleGraph V) [DecidableRel G.Adj] :
    (V → ℝ) →ₗ[ℝ] (Sym2 V → ℝ) :=
  ∑ u : V, (LinearMap.proj u).smulRight (averagedPivot G u)

theorem incidence_triangleInverse (G : SimpleGraph V) [DecidableRel G.Adj]
    (hpos : ∀ u, 0 < (trianglePairs G u).card) (x : V → ℝ) :
    incidence G (triangleInverse G x) = x := by
  classical
  simp only [triangleInverse, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]
  rw [map_sum]
  simp only [map_smul, incidence_averagedPivot G _ (hpos _)]
  funext z
  simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, mul_ite]

#print axioms incidence_pivot
#print axioms incidence_averagedPivot
#print axioms incidence_triangleInverse

end PartitionedTriangleAbsorption.F0Direct.SignlessTriangle
