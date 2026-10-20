/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.MatrixSections
public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.LocalProfiles

@[expose] public section

/-! A bounded linear section for the actual local-profile matrix. The constant
is selected before the host, and the coefficients sum to zero in each class.
This supplies vertex-mode coefficients, not the assembled triangle inverse. -/
noncomputable section
namespace PaddedGeneral
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

def finiteLocalProfileMap (F : Finset (Multiset (Fin 4))) (i : Fin 4) :
    ((F.filter fun τ => i ∈ τ) → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun c := ∑ τ, c τ • (fun j => (typeDegVec τ.val i j : ℝ))
  map_add' c d := by simp [add_smul, sum_add_distrib]
  map_smul' a c := by simp [mul_smul, smul_sum]

/-- The constant depends only on F and the root label, never on the graph or
the demand. Exact typeDegVec columns retain every repeated-label multiplicity. -/
theorem exists_bounded_local_profile_section (F : Finset (Multiset (Fin 4))) (i : Fin 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin 4) (r : Sym2 V → ℝ), LocalSpanCompat p F r →
      (∀ j, classTotal p (fun a b => r s(a,b)) i j = 0) →
      ∃ c : (classVertices p i) → (F.filter fun τ => i ∈ τ) → ℝ,
        (∀ v, finiteLocalProfileMap F i (c v) =
          classRow p (fun a b => r s(a,b)) v.val) ∧
        (∑ v, c v = 0) ∧
        (∀ v, ‖c v‖ ≤ C * ‖classRow p (fun a b => r s(a,b)) v.val‖) := by
  classical
  let f := finiteLocalProfileMap F i
  obtain ⟨s, C, hC, hs, hb⟩ := TypedMatrixSections.real_section f
  refine ⟨C, hC, ?_⟩
  intro V _ _ p r hr hzero
  have hd (v : classVertices p i) :
      classRow p (fun a b => r s(a,b)) v.val ∈ f.range := by
    obtain ⟨d, hd⟩ := hr v.val
    have hv : p v.val = i := (mem_classVertices p i v.val).mp v.property
    refine ⟨fun τ => d τ.val, ?_⟩
    rw [hv] at hd
    change (∑ τ : (F.filter fun τ => i ∈ τ),
      d τ.val • (fun j => (typeDegVec τ.val i j : ℝ))) = _
    exact (sum_coe_sort (F.filter fun τ => i ∈ τ)
      (fun τ => d τ • (fun j => (typeDegVec τ i j : ℝ)))).trans hd.symm
  let q : (classVertices p i) → f.range := fun v =>
    ⟨classRow p (fun a b => r s(a,b)) v.val, hd v⟩
  have hq : ∑ v, q v = 0 := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_zero]
    change (∑ v : classVertices p i,
      classRow p (fun a b => r s(a,b)) v.val) = 0
    rw [sum_coe_sort (classVertices p i) (classRow p (fun a b => r s(a,b)))]
    funext j
    simp only [Finset.sum_apply, Pi.zero_apply]
    exact hzero j
  refine ⟨fun v => s (q v), fun v => hs (q v), ?_, fun v => hb (q v)⟩
  rw [← map_sum, hq, map_zero]

#print axioms exists_bounded_local_profile_section
end PaddedGeneral
