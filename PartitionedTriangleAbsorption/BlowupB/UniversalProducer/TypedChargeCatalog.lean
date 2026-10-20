/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.ChargeAtoms
public import PartitionedTriangleAbsorption.TypedDivisibilityCollapse
public import Mathlib.GroupTheory.QuotientGroup.Defs

@[expose] public section

/-! The charge catalog in the ACTUAL integral type quotient. It retains
torsion; replacing this group by a real cokernel would lose information.
This connects the algebraic grouping step, not the physical shared library. -/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset TypedTransformer TypedDivisibilityCollapse AntiEdgeSelection

variable {t : ℕ}

def globalTypeHom (F : Finset (Multiset (Fin t))) :
    (Multiset (Fin t) → ℤ) →+ (Fin t → Fin t → ℤ) where
  toFun c := ∑ τ ∈ F, c τ • typeEdgeVec τ
  map_zero' := by simp
  map_add' c d := by simp [add_smul, sum_add_distrib]

abbrev TypeChargeGroup (F : Finset (Multiset (Fin t))) :=
  (Fin t → Fin t → ℤ) ⧸ (globalTypeHom F).range

def globalCharge (F : Finset (Multiset (Fin t))) :
    (Fin t → Fin t → ℤ) →+ TypeChargeGroup F :=
  QuotientAddGroup.mk' (globalTypeHom F).range

theorem globalCharge_eq_zero_iff (F : Finset (Multiset (Fin t)))
    (v : Fin t → Fin t → ℤ) :
    globalCharge F v = 0 ↔ ∃ c : Multiset (Fin t) → ℤ,
      v = ∑ τ ∈ F, c τ • typeEdgeVec τ := by
  change (QuotientAddGroup.mk v : TypeChargeGroup F) = 0 ↔ _
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, hc.symm⟩

theorem isIntDiv_iff_charge_zero {V : Type*} [DecidableEq V]
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (hthree : ThreeStepLinks F) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hactive : ActiveEdges F p E)
    (heven : ∀ v, Even (incidentLoad E v)) :
    IsIntDiv p F E ↔ globalCharge F (edgeVec p E) = 0 := by
  rw [globalCharge_eq_zero_iff]
  exact ⟨fun h => h.1, fun h => isIntDiv_of_active_even hthree hloop hactive heven h⟩

def naturalTypeSum {I : Type*} [Fintype I] (v : I → Fin t → Fin t → ℤ) :
    (I → ℕ) →+ (Fin t → Fin t → ℤ) where
  toFun x := ∑ i, x i • v i
  map_zero' := by simp
  map_add' x y := by
    simp only [Pi.add_apply, add_nsmul, Finset.sum_add_distrib]

/-- For any finite preliminary piece-type list, the recipe catalog precedes
all multiplicities (and therefore all host sizes and all leftovers).
Physical routing and simultaneous library incidence are NOT asserted. -/
theorem exists_typed_charge_catalog {I : Type*} [Fintype I]
    (F : Finset (Multiset (Fin t))) (v : I → Fin t → Fin t → ℤ) :
    ∃ (catalog : Finset (I → ℕ)) (K : ℕ), 0 < K ∧
      (∀ a ∈ catalog,
        globalCharge F (naturalTypeSum v a) = 0 ∧ chargeMass a ≤ K) ∧
      ∀ x, globalCharge F (naturalTypeSum v x) = 0 →
        ∃ l : List (I → ℕ), l.sum = x ∧ ∀ a ∈ l, a ∈ catalog := by
  obtain ⟨catalog, K, hK, ha, hx⟩ :=
    exists_bounded_charge_catalog ((globalCharge F).comp (naturalTypeSum v))
  refine ⟨catalog, K, hK, fun a h => ?_, hx⟩
  exact ⟨(ha a h).1.1.2, (ha a h).2⟩

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer

#print axioms PartitionedTriangleAbsorption.BlowupB.UniversalProducer.globalCharge_eq_zero_iff
#print axioms PartitionedTriangleAbsorption.BlowupB.UniversalProducer.isIntDiv_iff_charge_zero
#print axioms PartitionedTriangleAbsorption.BlowupB.UniversalProducer.exists_typed_charge_catalog
