/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteAlgebra

@[expose] public section

/-! # Linearity of all three stages of complete-crossing repair -/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete

open Finset

variable {A B EA EB : Type*}
variable [Fintype A] [Fintype B] [Fintype EA] [Fintype EB]

theorem firstResidual_add (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (g h : Demand A B EA EB) (uv : A × B) :
    firstResidual IA IB (g + h) uv = firstResidual IA IB g uv + firstResidual IA IB h uv := by
  simp only [firstResidual, crossLoad, firstWeights, inc, LinearMap.coe_mk,
    AddHom.coe_mk, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_div, mul_add,
    Finset.sum_add_distrib]
  ring

theorem firstResidual_smul (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (c : ℝ) (g : Demand A B EA EB) (uv : A × B) :
    firstResidual IA IB (c • g) uv = c * firstResidual IA IB g uv := by
  simp only [firstResidual, crossLoad, firstWeights, inc, LinearMap.coe_mk,
    AddHom.coe_mk, Prod.smul_def, Pi.smul_apply, smul_eq_mul]
  have hA : (∑ f : EA, IA uv.1 f * (c * g.1 f / Fintype.card B)) =
      c * ∑ f : EA, IA uv.1 f * (g.1 f / Fintype.card B) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro f _
    ring
  have hB : (∑ f : EB, IB uv.2 f * (c * g.2.1 f / Fintype.card A)) =
      c * ∑ f : EB, IB uv.2 f * (g.2.1 f / Fintype.card A) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro f _
    ring
  rw [hA, hB]
  ring

theorem rowResidual_add (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (g h : Demand A B EA EB) (u : A) :
    rowResidual IA IB (g + h) u = rowResidual IA IB g u + rowResidual IA IB h u := by
  simp only [rowResidual, firstResidual_add, sum_add_distrib]

theorem rowResidual_smul (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (c : ℝ) (g : Demand A B EA EB) (u : A) :
    rowResidual IA IB (c • g) u = c * rowResidual IA IB g u := by
  simp only [rowResidual, firstResidual_smul, Finset.mul_sum]

theorem finalResidual_add (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (g h : Demand A B EA EB) (uv : A × B) :
    finalResidual IA IB (g + h) uv = finalResidual IA IB g uv + finalResidual IA IB h uv := by
  simp only [finalResidual, firstResidual_add, rowResidual_add]
  ring

theorem finalResidual_smul (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (c : ℝ) (g : Demand A B EA EB) (uv : A × B) :
    finalResidual IA IB (c • g) uv = c * finalResidual IA IB g uv := by
  simp only [finalResidual, firstResidual_smul, rowResidual_smul]
  ring

theorem completeWeightsFun_add (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ)) (g h : Demand A B EA EB) :
    completeWeightsFun IA IB Q (g + h) =
      completeWeightsFun IA IB Q g + completeWeightsFun IA IB Q h := by
  apply Prod.ext
  · ext fv
    have hQ : Q (fun u => finalResidual IA IB (g + h) (u, fv.2)) =
        Q (fun u => finalResidual IA IB g (u, fv.2)) +
        Q (fun u => finalResidual IA IB h (u, fv.2)) := by
      convert Q.map_add (fun u => finalResidual IA IB g (u, fv.2))
        (fun u => finalResidual IA IB h (u, fv.2)) using 1
      congr 1
      ext u
      exact finalResidual_add IA IB g h (u, fv.2)
    simp only [completeWeightsFun, Prod.fst_add, Prod.snd_add, Pi.add_apply, hQ, add_div]
    ring
  · ext uf
    simp only [completeWeightsFun, Prod.fst_add, Prod.snd_add, Pi.add_apply,
      rowResidual_add, add_div]
    ring

theorem completeWeightsFun_smul (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ)) (c : ℝ) (g : Demand A B EA EB) :
    completeWeightsFun IA IB Q (c • g) = c • completeWeightsFun IA IB Q g := by
  apply Prod.ext
  · ext fv
    have hQ : Q (fun u => finalResidual IA IB (c • g) (u, fv.2)) =
        c • Q (fun u => finalResidual IA IB g (u, fv.2)) := by
      convert Q.map_smul c (fun u => finalResidual IA IB g (u, fv.2)) using 1
      congr 1
      ext u
      exact finalResidual_smul IA IB c g (u, fv.2)
    change (c • g).1 fv.1 / Fintype.card B +
      Q (fun u => finalResidual IA IB (c • g) (u, fv.2)) fv.1 = _
    rw [hQ]
    simp only [completeWeightsFun, Prod.smul_def, Pi.smul_apply, smul_eq_mul]
    ring
  · ext uf
    change (c • g).2.1 uf.2 / Fintype.card A +
      rowResidual IA IB (c • g) uf.1 / (2 * Fintype.card EB) = _
    rw [rowResidual_smul]
    simp only [completeWeightsFun, Prod.smul_def, Pi.smul_apply, smul_eq_mul]
    ring

/-- The complete-host inverse is a single linear map fixed before the demand. -/
noncomputable def completeWeights (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ)) :
    Demand A B EA EB →ₗ[ℝ] Weights A B EA EB where
  toFun := completeWeightsFun IA IB Q
  map_add' := completeWeightsFun_add IA IB Q
  map_smul' c g := by
    simpa only [RingHom.id_apply] using completeWeightsFun_smul IA IB Q c g

#print axioms completeWeights

end PartitionedTriangleAbsorption.F0Direct.RealComplete
