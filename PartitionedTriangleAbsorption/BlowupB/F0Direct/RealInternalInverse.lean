/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.SignlessSupport
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteCoordinates

@[expose] public section

/-! # The explicit internal inverse on actual internal edge coordinates -/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete.Internal

open Finset BalancedLinearRepair

variable {A : Type*} [Fintype A] [DecidableEq A]
variable (G : SimpleGraph A) [DecidableRel G.Adj]

noncomputable def matrix (u : A) (f : HostEdge G) : ℝ := G.incMatrix ℝ u f.val

noncomputable def restrict : (Sym2 A → ℝ) →ₗ[ℝ] (HostEdge G → ℝ) where
  toFun q f := q f.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inc_restrict (q : Sym2 A → ℝ) :
    inc (matrix G) (restrict G q) = SignlessTriangle.incidence G q := by
  classical
  ext u
  change (∑ f : HostEdge G, G.incMatrix ℝ u f.val * q f.val) =
    ∑ f : Sym2 A, G.incMatrix ℝ u f * q f
  rw [← Finset.sum_subtype G.edgeFinset (fun _ => Iff.rfl)
    (fun f => G.incMatrix ℝ u f * q f)]
  apply Finset.sum_subset (subset_univ _)
  intro f _ hf
  have he : f ∉ G.edgeSet := by simpa only [← SimpleGraph.mem_edgeFinset] using hf
  have hz : G.incMatrix ℝ u f = 0 :=
    G.incMatrix_of_notMem_incidenceSet (fun h => he h.1)
  rw [hz, zero_mul]

theorem matrix_column_sum (f : HostEdge G) : (∑ u, matrix G u f) = 2 :=
  G.sum_incMatrix_apply_of_mem_edgeSet (R := ℝ) (SimpleGraph.mem_edgeFinset.mp f.property)

theorem matrix_row_bound (u : A) : (∑ f : HostEdge G, |matrix G u f|) ≤ Fintype.card A := by
  classical
  have habs (f : HostEdge G) : |matrix G u f| = matrix G u f := by
    simp only [matrix, SimpleGraph.incMatrix_apply']
    split_ifs <;> norm_num
  simp only [habs]
  have heq := congrArg (fun x : A → ℝ => x u) (inc_restrict G (fun _ => 1))
  simp only [inc, matrix, restrict, SignlessTriangle.incidence, LinearMap.coe_mk,
    AddHom.coe_mk, mul_one] at heq
  change (∑ f : HostEdge G, G.incMatrix ℝ u f.val) ≤ Fintype.card A
  rw [heq, G.sum_incMatrix_apply (R := ℝ)]
  exact_mod_cast (G.degree_lt_card_verts u).le

noncomputable def inverse : (A → ℝ) →ₗ[ℝ] (HostEdge G → ℝ) :=
  (restrict G).comp (SignlessTriangle.triangleInverse G)

theorem inverse_exact (hcount : ∀ u, 0 < (SignlessTriangle.trianglePairs G u).card)
    (x : A → ℝ) : inc (matrix G) (inverse G x) = x := by
  change inc (matrix G) (restrict G (SignlessTriangle.triangleInverse G x)) = x
  rw [inc_restrict]
  exact SignlessTriangle.incidence_triangleInverse G hcount x

theorem inverse_bound_global (n tau : ℝ) (hn : 0 < n) (htau : 0 < tau)
    (hcard : (Fintype.card A : ℝ) ≤ n)
    (hcount : ∀ u, 2 * tau * n ^ 2 ≤ ((SignlessTriangle.trianglePairs G u).card : ℝ))
    (x : A → ℝ) (M : ℝ) (hM : 0 ≤ M) (hx : ∀ u, |x u| ≤ M)
    (f : HostEdge G) : |inverse G x f| ≤ (3 / (2 * tau)) * M / n := by
  have hb := SignlessTriangle.triangleInverse_abs_le_global_order G n tau M hn htau hM
    hcard hcount x hx f.val
  change |SignlessTriangle.triangleInverse G x f.val| ≤ _
  convert hb using 1 <;> ring

#print axioms matrix_column_sum
#print axioms matrix_row_bound
#print axioms inverse_exact
#print axioms inverse_bound_global

end PartitionedTriangleAbsorption.F0Direct.RealComplete.Internal
