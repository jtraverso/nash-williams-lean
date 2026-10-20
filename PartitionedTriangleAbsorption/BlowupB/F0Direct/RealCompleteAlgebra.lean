/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.LinearRepair
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Algebra.BigOperators.Field

@[expose] public section

/-!
# Exact real repair with complete crossing edges

This module proves the three algebraic stages of the inverse independently
of enumeration of physical copies. `A,B` are vertex sets and `EA,EB` are
actual internal edge sets. Their incidence matrices have column sum two.
The weight indices are precisely `(EA × B) ⊕ (A × EB)`.
-/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete

open Finset

variable {A B EA EB : Type*}
variable [Fintype A] [Fintype B] [Fintype EA] [Fintype EB]

abbrev Demand (A B EA EB : Type*) :=
  (EA → ℝ) × (EB → ℝ) × (A × B → ℝ)

abbrev Weights (A B EA EB : Type*) :=
  (EA × B → ℝ) × (A × EB → ℝ)

noncomputable def inc (I : A → EA → ℝ) : (EA → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun x u := ∑ f, I u f * x f
  map_add' x y := by ext u; simp [mul_add, sum_add_distrib]
  map_smul' c x := by
    ext u
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp only [Finset.mul_sum]
    apply sum_congr rfl
    intro f _
    ring

noncomputable def degree (I : B → EB → ℝ) (v : B) : ℝ := ∑ f, I v f

noncomputable def crossLoad (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (w : Weights A B EA EB) (uv : A × B) : ℝ :=
  (inc IA (fun f => w.1 (f, uv.2))) uv.1 +
  (inc IB (fun f => w.2 (uv.1, f))) uv.2

noncomputable def internalLoadA (w : Weights A B EA EB) (f : EA) : ℝ :=
  ∑ v : B, w.1 (f, v)

noncomputable def internalLoadB (w : Weights A B EA EB) (f : EB) : ℝ :=
  ∑ u : A, w.2 (u, f)

def Balanced (g : Demand A B EA EB) : Prop :=
  (∑ uv : A × B, g.2.2 uv) = 2 * ((∑ f, g.1 f) + ∑ f, g.2.1 f)

noncomputable def firstWeights (g : Demand A B EA EB) : Weights A B EA EB :=
  (fun fv => g.1 fv.1 / Fintype.card B,
   fun uf => g.2.1 uf.2 / Fintype.card A)

noncomputable def firstResidual (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (g : Demand A B EA EB) (uv : A × B) : ℝ :=
  g.2.2 uv - crossLoad IA IB (firstWeights g) uv

noncomputable def rowResidual (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (g : Demand A B EA EB) (u : A) : ℝ :=
  ∑ v : B, firstResidual IA IB g (u, v)

noncomputable def finalResidual (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (g : Demand A B EA EB) (uv : A × B) : ℝ :=
  firstResidual IA IB g uv -
    rowResidual IA IB g uv.1 * degree IB uv.2 / (2 * Fintype.card EB)

noncomputable def completeWeightsFun (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ))
    (g : Demand A B EA EB) : Weights A B EA EB :=
  (fun fv => g.1 fv.1 / Fintype.card B +
      Q (fun u => finalResidual IA IB g (u, fv.2)) fv.1,
   fun uf => g.2.1 uf.2 / Fintype.card A +
      rowResidual IA IB g uf.1 / (2 * Fintype.card EB))

theorem inc_sum (I : A → EA → ℝ)
    (hcol : ∀ f, (∑ u, I u f) = 2) (x : EA → ℝ) :
    (∑ u, inc I x u) = 2 * ∑ f, x f := by
  simp only [inc, LinearMap.coe_mk, AddHom.coe_mk]
  rw [sum_comm]
  simp only [← Finset.sum_mul, hcol, Finset.mul_sum]

theorem degree_sum (I : B → EB → ℝ)
    (hcol : ∀ f, (∑ v, I v f) = 2) :
    (∑ v, degree I v) = 2 * (Fintype.card EB : ℝ) := by
  simp only [degree]
  rw [sum_comm]
  simp [hcol, mul_comm]

theorem firstWeights_internalA (g : Demand A B EA EB)
    (hB : (Fintype.card B : ℝ) ≠ 0) (f : EA) :
    internalLoadA (firstWeights g) f = g.1 f := by
  simp only [internalLoadA, firstWeights, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem firstWeights_internalB (g : Demand A B EA EB)
    (hA : (Fintype.card A : ℝ) ≠ 0) (f : EB) :
    internalLoadB (firstWeights g) f = g.2.1 f := by
  simp only [internalLoadB, firstWeights, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem total_crossLoad (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (hA : ∀ f, (∑ u, IA u f) = 2) (hB : ∀ f, (∑ v, IB v f) = 2)
    (w : Weights A B EA EB) :
    (∑ uv : A × B, crossLoad IA IB w uv) =
      2 * ((∑ f, internalLoadA w f) + ∑ f, internalLoadB w f) := by
  simp only [Fintype.sum_prod_type, crossLoad, sum_add_distrib]
  have hleft : (∑ u : A, ∑ v : B, inc IA (fun f => w.1 (f, v)) u) =
      2 * ∑ f, internalLoadA w f := by
    rw [sum_comm]
    simp only [inc_sum IA hA, ← Finset.mul_sum]
    congr 1
    exact sum_comm
  have hright : (∑ u : A, ∑ v : B, inc IB (fun f => w.2 (u, f)) v) =
      2 * ∑ f, internalLoadB w f := by
    simp only [inc_sum IB hB, ← Finset.mul_sum]
    congr 1
    exact sum_comm
  rw [hleft, hright]
  ring

theorem firstResidual_sum (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (hIA : ∀ f, (∑ u, IA u f) = 2) (hIB : ∀ f, (∑ v, IB v f) = 2)
    (hA : (Fintype.card A : ℝ) ≠ 0) (hB : (Fintype.card B : ℝ) ≠ 0)
    (g : Demand A B EA EB) (hg : Balanced g) :
    (∑ uv, firstResidual IA IB g uv) = 0 := by
  simp only [firstResidual, sum_sub_distrib]
  rw [total_crossLoad IA IB hIA hIB]
  simp only [firstWeights_internalA g hB, firstWeights_internalB g hA]
  exact sub_eq_zero.mpr hg

theorem rowResidual_sum (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (hIA : ∀ f, (∑ u, IA u f) = 2) (hIB : ∀ f, (∑ v, IB v f) = 2)
    (hA : (Fintype.card A : ℝ) ≠ 0) (hB : (Fintype.card B : ℝ) ≠ 0)
    (g : Demand A B EA EB) (hg : Balanced g) :
    (∑ u, rowResidual IA IB g u) = 0 := by
  simpa only [rowResidual, ← Fintype.sum_prod_type] using
    firstResidual_sum IA IB hIA hIB hA hB g hg

theorem finalResidual_row_sum (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (hIB : ∀ f, (∑ v, IB v f) = 2)
    (heB : (Fintype.card EB : ℝ) ≠ 0)
    (g : Demand A B EA EB) (u : A) :
    (∑ v, finalResidual IA IB g (u, v)) = 0 := by
  simp only [finalResidual, sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  rw [degree_sum IB hIB]
  change rowResidual IA IB g u - rowResidual IA IB g u *
    (2 * (Fintype.card EB : ℝ)) / (2 * Fintype.card EB) = 0
  field_simp
  ring

theorem completeWeights_internalA (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ))
    (hIB : ∀ f, (∑ v, IB v f) = 2)
    (hB : (Fintype.card B : ℝ) ≠ 0) (heB : (Fintype.card EB : ℝ) ≠ 0)
    (g : Demand A B EA EB) (f : EA) :
    internalLoadA (completeWeightsFun IA IB Q g) f = g.1 f := by
  simp only [internalLoadA, completeWeightsFun, sum_add_distrib]
  have hfirst : (∑ _v : B, g.1 f / Fintype.card B) = g.1 f := by
    simp only [sum_const, card_univ, nsmul_eq_mul]
    field_simp
  have hzero : (∑ v : B, Q (fun u => finalResidual IA IB g (u, v))) = 0 := by
    rw [← map_sum]
    have hx : (∑ v : B, fun u => finalResidual IA IB g (u, v)) = 0 := by
      ext u
      simp only [Finset.sum_apply, Pi.zero_apply, finalResidual_row_sum IA IB hIB heB g]
    rw [hx, map_zero]
  rw [hfirst]
  have hz := congrArg (fun x : EA → ℝ => x f) hzero
  simp only [Finset.sum_apply, Pi.zero_apply] at hz
  rw [hz, add_zero]

theorem completeWeights_internalB (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ))
    (hIA : ∀ f, (∑ u, IA u f) = 2) (hIB : ∀ f, (∑ v, IB v f) = 2)
    (hA : (Fintype.card A : ℝ) ≠ 0) (hB : (Fintype.card B : ℝ) ≠ 0)
    (g : Demand A B EA EB) (hg : Balanced g) (f : EB) :
    internalLoadB (completeWeightsFun IA IB Q g) f = g.2.1 f := by
  simp only [internalLoadB, completeWeightsFun, sum_add_distrib,
    ← Finset.sum_div, rowResidual_sum IA IB hIA hIB hA hB g hg, zero_div,
    add_zero, sum_const, card_univ, nsmul_eq_mul]
  field_simp

theorem completeWeights_cross (IA : A → EA → ℝ) (IB : B → EB → ℝ)
    (Q : (A → ℝ) →ₗ[ℝ] (EA → ℝ))
    (hQ : ∀ x, inc IA (Q x) = x)
    (g : Demand A B EA EB) (uv : A × B) :
    crossLoad IA IB (completeWeightsFun IA IB Q g) uv = g.2.2 uv := by
  have hleft : inc IA (fun f => (completeWeightsFun IA IB Q g).1 (f, uv.2)) uv.1 =
      inc IA (fun f => g.1 f / Fintype.card B) uv.1 + finalResidual IA IB g uv := by
    change inc IA ((fun f => g.1 f / Fintype.card B) +
      Q (fun u => finalResidual IA IB g (u, uv.2))) uv.1 = _
    rw [map_add, hQ]
    rfl
  have hright : inc IB (fun f => (completeWeightsFun IA IB Q g).2 (uv.1, f)) uv.2 =
      inc IB (fun f => g.2.1 f / Fintype.card A) uv.2 +
        rowResidual IA IB g uv.1 * degree IB uv.2 / (2 * Fintype.card EB) := by
    simp only [inc, completeWeightsFun, LinearMap.coe_mk, AddHom.coe_mk,
      mul_add, sum_add_distrib, degree]
    congr 1
    rw [← Finset.sum_mul]
    ring
  unfold crossLoad
  rw [hleft, hright]
  simp only [finalResidual, firstResidual, crossLoad, firstWeights]
  ring

#print axioms completeWeights_internalA
#print axioms completeWeights_internalB
#print axioms completeWeights_cross

end PartitionedTriangleAbsorption.F0Direct.RealComplete
