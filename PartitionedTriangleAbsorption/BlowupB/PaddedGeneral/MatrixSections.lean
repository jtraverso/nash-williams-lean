/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Module.Projective
import Mathlib.Tactic

/-! Sections of the actual image of a fixed matrix. In particular, neither
global compatibility nor a local profile compatibility may be omitted.
Both sections are linear and bounded on the actual image. The integral estimate
uses Smith normal form and retains integral, not merely real, compatibility. -/

namespace TypedMatrixSections

open Finset

theorem real_section {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E →ₗ[ℝ] F) :
    ∃ (s : f.range →ₗ[ℝ] E) (C : ℝ), 0 < C ∧
      (∀ y, f (s y) = y.val) ∧ (∀ y, ‖s y‖ ≤ C * ‖y.val‖) := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  let sc : f.range →L[ℝ] E := ⟨s, s.continuous_of_finiteDimensional⟩
  obtain ⟨C, hC, hb⟩ := sc.bound
  refine ⟨s, C, hC, ?_, hb⟩
  intro y
  exact congrArg Subtype.val (DFunLike.congr_fun hs y)

/-- The same section handles every root, so zero sums stay zero without an
anchor correction. The bound is per root, not just on the total mass. -/
theorem real_balanced_section {I E F : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (f : E →ₗ[ℝ] F) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : I → F),
      (∀ i, d i ∈ f.range) → (∑ i, d i = 0) →
      ∃ c : I → E, (∀ i, f (c i) = d i) ∧
        (∑ i, c i = 0) ∧ (∀ i, ‖c i‖ ≤ C * ‖d i‖) := by
  obtain ⟨s, C, hC, hs, hb⟩ := real_section f
  refine ⟨C, hC, fun d hd hz => ?_⟩
  let q : I → f.range := fun i => ⟨d i, hd i⟩
  have hq : ∑ i, q i = 0 := by
    apply Subtype.ext
    simpa [q] using hz
  refine ⟨fun i => s (q i), fun i => hs (q i), ?_, fun i => hb (q i)⟩
  rw [← map_sum, hq, map_zero]

theorem integer_section {I J : Type*} [Fintype I] [Fintype J]
    (f : (I → ℤ) →ₗ[ℤ] (J → ℤ)) :
    ∃ s : f.range →ₗ[ℤ] (I → ℤ), ∀ y, f (s y) = y.val := by
  obtain ⟨s, hs⟩ := f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict
  exact ⟨s, fun y => congrArg Subtype.val (DFunLike.congr_fun hs y)⟩

#print axioms real_section
#print axioms real_balanced_section
#print axioms integer_section

def mass {I : Type*} [Fintype I] (x : I → ℤ) : ℤ := ∑ i, |x i|

theorem integer_linear_bound {I J : Type*} [Fintype I] [Fintype J]
    (f : (I → ℤ) →ₗ[ℤ] (J → ℤ)) :
    ∃ C : ℤ, 0 ≤ C ∧ ∀ x, mass (f x) ≤ C * mass x := by
  classical
  let e := Pi.basisFun ℤ I
  let C : ℤ := ∑ i, mass (f (e i))
  have hC : 0 ≤ C := sum_nonneg fun i _ => sum_nonneg fun j _ => abs_nonneg _
  refine ⟨C, hC, fun x => ?_⟩
  have hx : x = ∑ i, x i • e i := by simpa [e] using (e.sum_repr x).symm
  have hf (j : J) : f x j = ∑ i, x i * f (e i) j := by
    conv_lhs => rw [hx]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    mass (f x) ≤ ∑ j, ∑ i, |x i| * |f (e i) j| := by
      unfold mass
      apply sum_le_sum
      intro j _
      simpa [hf, abs_mul] using (Finset.abs_sum_le_sum_abs
        (fun i => x i * f (e i) j) univ)
    _ = ∑ i, |x i| * mass (f (e i)) := by
      rw [sum_comm]
      simp [mass, mul_sum]
    _ ≤ ∑ i, |x i| * C := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact single_le_sum (f := fun j => mass (f (e j)))
        (fun j _ => sum_nonneg fun k _ => abs_nonneg (f (e j) k)) (mem_univ i)
    _ = C * mass x := by simp [mass, sum_mul, mul_comm]

/-- Smith coordinates in a sublattice cannot be larger than the corresponding
ambient coordinates: each nonzero integral diagonal has absolute value at least one. -/
theorem smith_coordinate_bound {J : Type*} [Fintype J]
    {N : Submodule ℤ (J → ℤ)} {k : ℕ}
    (snf : Module.Basis.SmithNormalForm N J k) (y : N) :
    mass (snf.bN.equivFun y) ≤ mass (snf.bM.equivFun y.val) := by
  classical
  have ha (i : Fin k) : snf.a i ≠ 0 := by
    intro h
    have hz : (snf.bN i : J → ℤ) = 0 := by rw [snf.snf, h, zero_smul]
    exact snf.bN.ne_zero i (Subtype.ext hz)
  have hc (i : Fin k) : |snf.bN.repr y i| ≤ |snf.bM.repr y.val (snf.f i)| := by
    rw [snf.repr_apply_embedding_eq_repr_smul, map_smul, Finsupp.smul_apply,
      smul_eq_mul, abs_mul]
    have hi : (1 : ℤ) ≤ |snf.a i| := Int.one_le_abs (ha i)
    nlinarith [abs_nonneg (snf.bN.repr y i)]
  calc
    _ ≤ ∑ i, |snf.bM.repr y.val (snf.f i)| := sum_le_sum fun i _ => hc i
    _ ≤ ∑ j, |snf.bM.repr y.val j| := by
      rw [← Finset.sum_image (s := (univ : Finset (Fin k)))
        (f := fun j => |snf.bM.repr y.val j|)
        (fun _ _ _ _ h => snf.f.injective h)]
      exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
        (fun j _ _ => abs_nonneg (snf.bM.repr y.val j))
    _ = _ := rfl

/-- A genuine bounded integral section. Its constant depends only on the fixed
matrix, and the same linear section is used for every local profile. -/
theorem integer_bounded_section {I J : Type*} [Fintype I] [Fintype J]
    (f : (I → ℤ) →ₗ[ℤ] (J → ℤ)) :
    ∃ (s : f.range →ₗ[ℤ] (I → ℤ)) (C : ℤ), 0 ≤ C ∧
      (∀ y, f (s y) = y.val) ∧ (∀ y, mass (s y) ≤ C * mass y.val) := by
  classical
  obtain ⟨s, hs⟩ := integer_section f
  obtain ⟨k, snf⟩ := f.range.smithNormalForm (Pi.basisFun ℤ J)
  obtain ⟨A, hA, hAb⟩ := integer_linear_bound
    (s.comp snf.bN.equivFun.symm.toLinearMap)
  obtain ⟨B, hB, hBb⟩ := integer_linear_bound snf.bM.equivFun.toLinearMap
  refine ⟨s, A * B, mul_nonneg hA hB, hs, fun y => ?_⟩
  calc
    mass (s y) ≤ A * mass (snf.bN.equivFun y) := by
      simpa using hAb (snf.bN.equivFun y)
    _ ≤ A * mass (snf.bM.equivFun y.val) :=
      mul_le_mul_of_nonneg_left (smith_coordinate_bound snf y) hA
    _ ≤ A * (B * mass y.val) := mul_le_mul_of_nonneg_left (hBb y.val) hA
    _ = (A * B) * mass y.val := by ring

#print axioms integer_linear_bound
#print axioms smith_coordinate_bound
#print axioms integer_bounded_section

/-- Integral profiles can be balanced with a bound at every individual root.
No correction at a distinguished root, and hence no extra root congestion, is needed. -/
theorem integer_balanced_section {R I J : Type*}
    [Fintype R] [Fintype I] [Fintype J]
    (f : (I → ℤ) →ₗ[ℤ] (J → ℤ)) :
    ∃ C : ℤ, 0 ≤ C ∧ ∀ (d : R → J → ℤ),
      (∀ v, d v ∈ f.range) → (∑ v, d v = 0) →
      ∃ c : R → I → ℤ, (∀ v, f (c v) = d v) ∧
        (∑ v, c v = 0) ∧ (∀ v, mass (c v) ≤ C * mass (d v)) := by
  obtain ⟨s, C, hC, hs, hb⟩ := integer_bounded_section f
  refine ⟨C, hC, fun d hd hz => ?_⟩
  let q : R → f.range := fun v => ⟨d v, hd v⟩
  have hq : ∑ v, q v = 0 := by
    apply Subtype.ext
    simpa [q] using hz
  refine ⟨fun v => s (q v), fun v => hs (q v), ?_, fun v => hb (q v)⟩
  rw [← map_sum, hq, map_zero]

#print axioms integer_balanced_section

end TypedMatrixSections
