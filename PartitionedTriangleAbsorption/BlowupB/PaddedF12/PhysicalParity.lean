/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalLattice
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.ParityEvaluation
import PartitionedTriangleAbsorption.OnePartDivisibility

/-!
# Physical parity evaluations for F1 and F2

The F2 numerator is even on its stated domain. Division by two therefore
commutes with disjoint unions on that domain, including negative numerators.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse

def intParity (z : ℤ) : ℕ := (z % 2).toNat

theorem intParity_lt (z : ℤ) : intParity z < 2 := by
  unfold intParity
  omega

theorem intParity_zero : intParity 0 = 0 := by decide

theorem intParity_eq_zero_iff (z : ℤ) : intParity z = 0 ↔ (2 : ℤ) ∣ z := by
  rw [Int.dvd_iff_emod_eq_zero]
  unfold intParity
  omega

theorem intParity_add (z w : ℤ) :
    intParity (z + w) = (intParity z + intParity w) % 2 := by
  unfold intParity
  omega

variable {V : Type*} [DecidableEq V]

def F1Good (p : V → Fin 4) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ ActiveEdges F1 p E ∧
    (∀ v, Even (incidentLoad E v)) ∧ f1FreeCharge p E = 0

def F2Good (p : V → Fin 4) (E : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ E, ¬ e.IsDiag) ∧ ActiveEdges F2 p E ∧
    (∀ v, Even (incidentLoad E v)) ∧ f2FreeCharge p E = 0

def f1Bit (p : V → Fin 4) (E : Finset (Sym2 V)) : ℕ :=
  intParity (unorderedCount p E 0 2)

def f2Bit (p : V → Fin 4) (E : Finset (Sym2 V)) : ℕ :=
  intParity (f2Numerator p E / 2)

theorem F1Good_empty (p : V → Fin 4) : F1Good p ∅ := by
  simp [F1Good, ActiveEdges, OnePart.incidentLoad_empty, f1FreeCharge, freeCharge,
    f1Base, crossCount, unorderedCount_empty]

theorem F2Good_empty (p : V → Fin 4) : F2Good p ∅ := by
  simp [F2Good, ActiveEdges, OnePart.incidentLoad_empty, f2FreeCharge, freeCharge,
    f2Base, crossCount, unorderedCount_empty]

theorem F1Good_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B)
    (hA : F1Good p A) (hB : F1Good p B) : F1Good p (A ∪ B) := by
  refine ⟨?_, ?_, OnePart.even_incidentLoad_union h hA.2.2.1 hB.2.2.1, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hA.1 e he
    · exact hB.1 e he
  · intro a b hab
    rcases mem_union.mp hab with hab | hab
    · exact hA.2.1 a b hab
    · exact hB.2.1 a b hab
  · rw [f1FreeCharge_union p h, hA.2.2.2, hB.2.2.2, add_zero]

theorem F2Good_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B)
    (hA : F2Good p A) (hB : F2Good p B) : F2Good p (A ∪ B) := by
  refine ⟨?_, ?_, OnePart.even_incidentLoad_union h hA.2.2.1 hB.2.2.1, ?_⟩
  · intro e he
    rcases mem_union.mp he with he | he
    · exact hA.1 e he
    · exact hB.1 e he
  · intro a b hab
    rcases mem_union.mp hab with hab | hab
    · exact hA.2.1 a b hab
    · exact hB.2.1 a b hab
  · rw [f2FreeCharge_union p h, hA.2.2.2, hB.2.2.2, add_zero]

theorem f1Bit_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    f1Bit p (A ∪ B) = (f1Bit p A + f1Bit p B) % 2 := by
  simp only [f1Bit, unorderedCount_union p h, intParity_add]

theorem f2Bit_union [Fintype V] (p : V → Fin 4) {A B : Finset (Sym2 V)}
    (h : Disjoint A B) (hA : F2Good p A) (hB : F2Good p B) :
    f2Bit p (A ∪ B) = (f2Bit p A + f2Bit p B) % 2 := by
  obtain ⟨a, ha⟩ := f2Numerator_even p A hA.2.1 hA.1 hA.2.2.1
  obtain ⟨b, hb⟩ := f2Numerator_even p B hB.2.1 hB.1 hB.2.2.1
  have hsum : f2Numerator p (A ∪ B) / 2 = f2Numerator p A / 2 + f2Numerator p B / 2 := by
    rw [f2Numerator_union p h]
    omega
  simp only [f2Bit, hsum, intParity_add]

def f1Parity (p : V → Fin 4) : ParityEvaluation (F1Good p) where
  empty_good := F1Good_empty p
  union_good := F1Good_union p
  value := f1Bit p
  value_lt := fun E _ => intParity_lt _
  empty_value := by simp [f1Bit, unorderedCount_empty, intParity_zero]
  union_value := fun h _ _ => f1Bit_union p h

def f2Parity [Fintype V] (p : V → Fin 4) : ParityEvaluation (F2Good p) where
  empty_good := F2Good_empty p
  union_good := F2Good_union p
  value := f2Bit p
  value_lt := fun E _ => intParity_lt _
  empty_value := by simp [f2Bit, f2Numerator, unorderedCount_empty, intParity_zero]
  union_value := f2Bit_union p

theorem isIntDiv_F1_iff_bit [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hgood : F1Good p E) : IsIntDiv p F1 E ↔ f1Bit p E = 0 := by
  rw [isIntDiv_F1_iff_counts p E hgood.1 hgood.2.1]
  simp only [hgood.2.2.1, hgood.2.2.2, implies_true, true_and, f1Bit, intParity_eq_zero_iff]

theorem isIntDiv_F2_iff_bit [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hgood : F2Good p E) : IsIntDiv p F2 E ↔ f2Bit p E = 0 := by
  rw [isIntDiv_F2_iff_counts p E hgood.1 hgood.2.1]
  simp only [hgood.2.2.1, hgood.2.2.2, implies_true, true_and, f2Bit, intParity_eq_zero_iff]
  exact f2_torsion_iff (unorderedCount p E 0 0) _ _
    (f2_class_cut_parities p E hgood.2.1 hgood.1 hgood.2.2.1).1

theorem isIntDiv_F1_iff_good_bit [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F1 E ↔ F1Good p E ∧ f1Bit p E = 0 := by
  constructor
  · intro hd
    obtain ⟨hact, heven, _⟩ := (TypedPieceConditions.F1_isIntDiv_iff hloop).mp hd
    have hc := ((isIntDiv_F1_iff_counts p E hloop hact).mp hd).2.1
    have hg : F1Good p E := ⟨hloop, hact, heven, hc⟩
    exact ⟨hg, (isIntDiv_F1_iff_bit p E hg).mp hd⟩
  · rintro ⟨hg, hb⟩
    exact (isIntDiv_F1_iff_bit p E hg).mpr hb

theorem isIntDiv_F2_iff_good_bit [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F2 E ↔ F2Good p E ∧ f2Bit p E = 0 := by
  constructor
  · intro hd
    obtain ⟨hact, heven, _⟩ := (TypedPieceConditions.F2_isIntDiv_iff hloop).mp hd
    have hc := ((isIntDiv_F2_iff_counts p E hloop hact).mp hd).2.1
    have hg : F2Good p E := ⟨hloop, hact, heven, hc⟩
    exact ⟨hg, (isIntDiv_F2_iff_bit p E hg).mp hd⟩
  · rintro ⟨hg, hb⟩
    exact (isIntDiv_F2_iff_bit p E hg).mpr hb

#print axioms f1Parity
#print axioms f2Parity
#print axioms isIntDiv_F1_iff_bit
#print axioms isIntDiv_F2_iff_bit
#print axioms isIntDiv_F1_iff_good_bit
#print axioms isIntDiv_F2_iff_good_bit

end PaddedF12
