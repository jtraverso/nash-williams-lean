/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.BoundedProfiles

@[expose] public section

/-! Pointwise budgets for the real sections used by the general inverse.
Constants are chosen before the vertex type, partition and demand. These are
coefficient producers, not an assertion of the complete physical inverse. -/
noncomputable section
namespace PaddedGeneral
open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

theorem exists_uniform_profile_coefficients (F : Finset (Multiset (Fin 4))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin 4) (r : Sym2 V → ℝ) (ε : ℝ),
      0 ≤ ε → (∀ e, |r e| ≤ ε) → LocalSpanCompat p F r →
      ∀ i, (∀ j, classTotal p (fun a b => r s(a,b)) i j = 0) →
      ∃ c : (classVertices p i) → (F.filter fun τ => i ∈ τ) → ℝ,
        (∀ v, finiteLocalProfileMap F i (c v) =
          classRow p (fun a b => r s(a,b)) v.val) ∧
        (∑ v, c v = 0) ∧
        (∀ v τ, |c v τ| ≤ C * (Fintype.card V : ℝ) * ε) := by
  classical
  choose B hBpos hB using exists_bounded_local_profile_section F
  let C : ℝ := 1 + ∑ i : Fin 4, B i
  have hC : 0 < C := by
    have : 0 ≤ ∑ i : Fin 4, B i := sum_nonneg fun i _ => (hBpos i).le
    dsimp [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro V _ _ p r ε hε hr hc i hz
  obtain ⟨c,heq,hzero,hbound⟩ := hB i V p r hc hz
  refine ⟨c,heq,hzero,?_⟩
  have hBi : B i ≤ C := by
    have := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) => (hBpos j).le)
      (mem_univ i)
    dsimp [C]
    linarith
  intro v τ
  have hp : ‖classRow p (fun a b => r s(a,b)) v.val‖ ≤
      (Fintype.card V : ℝ) * ε := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    simpa only [Real.norm_eq_abs] using
      classRow_bound p (fun a b => r s(a,b)) ε hε (fun a b => hr s(a,b)) v.val j
  calc
    |c v τ| ≤ ‖c v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (c v) τ
    _ ≤ B i * ‖classRow p (fun a b => r s(a,b)) v.val‖ := hbound v
    _ ≤ B i * ((Fintype.card V : ℝ) * ε) := mul_le_mul_of_nonneg_left hp (hBpos i).le
    _ ≤ C * ((Fintype.card V : ℝ) * ε) := mul_le_mul_of_nonneg_right hBi (by positivity)
    _ = _ := by ring

def finiteGlobalProfileMap (F : Finset (Multiset (Fin 4))) :
    (F → ℝ) →ₗ[ℝ] (Fin 4 → Fin 4 → ℝ) where
  toFun c := ∑ τ, c τ • (fun i j => (typeEdgeVec τ.val i j : ℝ))
  map_add' c d := by simp [add_smul, sum_add_distrib]
  map_smul' a c := by simp [mul_smul, smul_sum]

theorem exists_bounded_global_coefficients (F : Finset (Multiset (Fin 4))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin 4) (r : Sym2 V → ℝ) (ε : ℝ),
      0 ≤ ε → (∀ e, |r e| ≤ ε) → SpanCompat p F r →
      ∃ c : F → ℝ,
        finiteGlobalProfileMap F c = classTotal p (fun a b => r s(a,b)) ∧
        ∀ τ, |c τ| ≤ C * ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  obtain ⟨s,C,hC,hs,hb⟩ := TypedMatrixSections.real_section (finiteGlobalProfileMap F)
  refine ⟨C,hC,?_⟩
  intro V _ _ p r ε hε hr hc
  obtain ⟨d,hd⟩ := hc
  have hy : classTotal p (fun a b => r s(a,b)) ∈ (finiteGlobalProfileMap F).range := by
    refine ⟨fun τ => d τ.val,?_⟩
    change (∑ τ : F, d τ.val • (fun i j => (typeEdgeVec τ.val i j : ℝ))) = _
    exact (sum_coe_sort F (fun τ => d τ • (fun i j => (typeEdgeVec τ i j : ℝ)))).trans hd.symm
  let y : (finiteGlobalProfileMap F).range := ⟨_,hy⟩
  refine ⟨s y,hs y,?_⟩
  have ht : ‖classTotal p (fun a b => r s(a,b))‖ ≤ ε * (Fintype.card V : ℝ)^2 := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    simpa only [Real.norm_eq_abs] using
      classTotal_bound p (fun a b => r s(a,b)) ε hε (fun a b => hr s(a,b)) i j
  intro τ
  calc
    |s y τ| ≤ ‖s y‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm (s y) τ
    _ ≤ C * ‖y.val‖ := hb y
    _ ≤ C * (ε * (Fintype.card V : ℝ)^2) := mul_le_mul_of_nonneg_left ht hC.le
    _ = _ := by ring

#print axioms exists_uniform_profile_coefficients
#print axioms exists_bounded_global_coefficients
end PaddedGeneral
