/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.ScalarLattice
import PartitionedTriangleAbsorption.TypedPieceConditions
import PartitionedTriangleAbsorption.TypedRefinerCharge

/-!
# Physical unordered counts and the original ordered edge vector

An internal physical edge contributes one to `unorderedCount` and two to a
diagonal entry of `edgeVec`.  All identifications below are proved from the
original definitions; no matrix or graph characterization is assumed.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse

variable {V : Type*} [DecidableEq V]

def unorderedCount (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) : ℤ :=
  ((E.filter (fun e => Sym2.map p e = s(i, j))).card : ℤ)

theorem unorderedCount_nonneg (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) :
    0 ≤ unorderedCount p E i j := by unfold unorderedCount; positivity

theorem unorderedCount_le_card (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) :
    unorderedCount p E i j ≤ E.card := by
  unfold unorderedCount
  exact_mod_cast (card_filter_le E (fun e => Sym2.map p e = s(i, j)))

theorem unorderedCount_swap (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) :
    unorderedCount p E i j = unorderedCount p E j i := by
  simp only [unorderedCount, Sym2.eq_swap]

theorem unorderedCount_empty (p : V → Fin 4) (i j : Fin 4) :
    unorderedCount p ∅ i j = 0 := by simp [unorderedCount]

theorem unorderedCount_union (p : V → Fin 4) {A B : Finset (Sym2 V)}
    (h : Disjoint A B) (i j : Fin 4) :
    unorderedCount p (A ∪ B) i j = unorderedCount p A i j + unorderedCount p B i j := by
  have h' : Disjoint (A.filter (fun e => Sym2.map p e = s(i, j)))
      (B.filter (fun e => Sym2.map p e = s(i, j))) :=
    h.mono (filter_subset _ _) (filter_subset _ _)
  simp only [unorderedCount, filter_union, card_union_of_disjoint h', Nat.cast_add]

theorem unorderedCount_sum (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) :
    unorderedCount p E i j = ∑ e ∈ E, if Sym2.map p e = s(i, j) then (1 : ℤ) else 0 := by
  simp only [unorderedCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

private theorem count_pair_identity : ∀ a b i j : Fin 4,
    (if a = i ∧ b = j then (1 : ℤ) else 0) +
      (if b = i ∧ a = j then (1 : ℤ) else 0) =
    (if i = j then (2 : ℤ) else 1) * (if s(a, b) = s(i, j) then 1 else 0) := by
  decide

theorem edgeVec_unorderedCount (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) :
    edgeVec p E i j = (if i = j then 2 else 1) * unorderedCount p E i j := by
  rw [unorderedCount_sum, mul_sum]
  simp only [edgeVec, Finset.sum_apply]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk, Sym2.map_mk]
    convert count_pair_identity (p a) (p b) i j using 1
    split_ifs <;> norm_num <;> simp_all only [Sym2.eq_iff] <;> tauto

theorem unorderedCount_zero_of_forbidden (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4)
    (h : ∀ e ∈ E, Sym2.map p e ≠ s(i, j)) : unorderedCount p E i j = 0 := by
  have hz : E.filter (fun e => Sym2.map p e = s(i, j)) = ∅ := filter_eq_empty_iff.mpr h
  simp only [unorderedCount, hz, card_empty, Nat.cast_zero]

theorem f1_inactive_counts (p : V → Fin 4) (E : Finset (Sym2 V))
    (h : ActiveEdges F1 p E) : unorderedCount p E 0 1 = 0 ∧ unorderedCount p E 2 3 = 0 := by
  have hf : ∀ a b k : Fin 4, Link F1 a b k → s(a, b) ≠ s(0, 1) ∧ s(a, b) ≠ s(2, 3) := by
    unfold Link; decide
  constructor
  · apply unorderedCount_zero_of_forbidden
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨k, hk⟩ := h a b he
      exact (hf (p a) (p b) k hk).1
  · apply unorderedCount_zero_of_forbidden
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨k, hk⟩ := h a b he
      exact (hf (p a) (p b) k hk).2

theorem f2_inactive_counts (p : V → Fin 4) (E : Finset (Sym2 V))
    (h : ActiveEdges F2 p E) : unorderedCount p E 0 1 = 0 ∧
      unorderedCount p E 2 2 = 0 ∧ unorderedCount p E 3 3 = 0 := by
  have hf : ∀ a b k : Fin 4, Link F2 a b k →
      s(a, b) ≠ s(0, 1) ∧ s(a, b) ≠ s(2, 2) ∧ s(a, b) ≠ s(3, 3) := by unfold Link; decide
  refine ⟨?_, ?_, ?_⟩
  · apply unorderedCount_zero_of_forbidden
    intro e he
    induction e using Sym2.ind with
    | _ a b => obtain ⟨k, hk⟩ := h a b he; exact (hf (p a) (p b) k hk).1
  · apply unorderedCount_zero_of_forbidden
    intro e he
    induction e using Sym2.ind with
    | _ a b => obtain ⟨k, hk⟩ := h a b he; exact (hf (p a) (p b) k hk).2.1
  · apply unorderedCount_zero_of_forbidden
    intro e he
    induction e using Sym2.ind with
    | _ a b => obtain ⟨k, hk⟩ := h a b he; exact (hf (p a) (p b) k hk).2.2

def f1Matrix (d0 d1 d2 d3 x02 x03 x12 x13 : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![2*d0, 0, x02, x03], ![0, 2*d1, x12, x13],
    ![x02, x12, 2*d2, 0], ![x03, x13, 0, 2*d3]]

def f2Matrix (d0 d1 x02 x03 x12 x13 x23 : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![2*d0, 0, x02, x03], ![0, 2*d1, x12, x13],
    ![x02, x12, 0, x23], ![x03, x13, x23, 0]]

theorem edgeVec_f1Matrix (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges F1 p E) :
    edgeVec p E = f1Matrix (unorderedCount p E 0 0) (unorderedCount p E 1 1)
      (unorderedCount p E 2 2) (unorderedCount p E 3 3) (unorderedCount p E 0 2)
      (unorderedCount p E 0 3) (unorderedCount p E 1 2) (unorderedCount p E 1 3) := by
  obtain ⟨h01, h23⟩ := f1_inactive_counts p E h
  funext i j
  rw [edgeVec_unorderedCount]
  fin_cases i <;> fin_cases j <;>
    simp [f1Matrix, unorderedCount_swap p E 1 0, unorderedCount_swap p E 2 0,
      unorderedCount_swap p E 2 1, unorderedCount_swap p E 3 0,
      unorderedCount_swap p E 3 1, unorderedCount_swap p E 3 2, h01, h23]

theorem edgeVec_f2Matrix (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges F2 p E) :
    edgeVec p E = f2Matrix (unorderedCount p E 0 0) (unorderedCount p E 1 1)
      (unorderedCount p E 0 2) (unorderedCount p E 0 3) (unorderedCount p E 1 2)
      (unorderedCount p E 1 3) (unorderedCount p E 2 3) := by
  obtain ⟨h01, h22, h33⟩ := f2_inactive_counts p E h
  funext i j
  rw [edgeVec_unorderedCount]
  fin_cases i <;> fin_cases j <;>
    simp [f2Matrix, unorderedCount_swap p E 1 0, unorderedCount_swap p E 2 0,
      unorderedCount_swap p E 2 1, unorderedCount_swap p E 3 0,
      unorderedCount_swap p E 3 1, unorderedCount_swap p E 3 2, h01, h22, h33]

def f1Base (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  unorderedCount p E 0 0 + unorderedCount p E 1 1 +
    unorderedCount p E 2 2 + unorderedCount p E 3 3

def f2Base (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  unorderedCount p E 0 0 + unorderedCount p E 1 1 + unorderedCount p E 2 3

def crossCount (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  unorderedCount p E 0 2 + unorderedCount p E 0 3 +
    unorderedCount p E 1 2 + unorderedCount p E 1 3

def f1FreeCharge (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  freeCharge (f1Base p E) (crossCount p E)

def f2FreeCharge (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  freeCharge (f2Base p E) (crossCount p E)

def f2Numerator (p : V → Fin 4) (E : Finset (Sym2 V)) : ℤ :=
  unorderedCount p E 0 2 - unorderedCount p E 0 3 + 2 * unorderedCount p E 0 0

theorem f1FreeCharge_eq_original (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges F1 p E) :
    f1FreeCharge p E = TypedRefinerCharge.charge TypedRefinerCharge.chi1 p E := by
  rw [TypedRefinerCharge.charge, edgeVec_f1Matrix p E h]
  simp [f1FreeCharge, freeCharge, f1Base, crossCount, TypedRefinerCharge.pair,
    TypedRefinerCharge.chi1, f1Matrix, Fin.sum_univ_succ]
  ring

theorem f2FreeCharge_eq_original (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges F2 p E) :
    f2FreeCharge p E = TypedRefinerCharge.charge TypedRefinerCharge.chi2 p E := by
  rw [TypedRefinerCharge.charge, edgeVec_f2Matrix p E h]
  simp [f2FreeCharge, freeCharge, f2Base, crossCount, TypedRefinerCharge.pair,
    TypedRefinerCharge.chi2, f2Matrix, Fin.sum_univ_succ]
  ring

theorem f1FreeCharge_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    f1FreeCharge p (A ∪ B) = f1FreeCharge p A + f1FreeCharge p B := by
  simp only [f1FreeCharge, freeCharge, f1Base, crossCount, unorderedCount_union p h]
  ring

theorem f2FreeCharge_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    f2FreeCharge p (A ∪ B) = f2FreeCharge p A + f2FreeCharge p B := by
  simp only [f2FreeCharge, freeCharge, f2Base, crossCount, unorderedCount_union p h]
  ring

theorem f2Numerator_union (p : V → Fin 4) {A B : Finset (Sym2 V)} (h : Disjoint A B) :
    f2Numerator p (A ∪ B) = f2Numerator p A + f2Numerator p B := by
  simp only [f2Numerator, unorderedCount_union p h]
  ring

theorem total_edgeVec (p : V → Fin 4) (E : Finset (Sym2 V)) :
    (∑ i, ∑ j, edgeVec p E i j) = 2 * E.card := by
  have he : ∀ e : Sym2 V, TypedRefinerCharge.pair (fun _ _ : Fin 4 => 1) (pairVec p e) = 2 := by
    intro e
    induction e using Sym2.ind with
    | _ a b => simp [TypedRefinerCharge.pair_pairVec]
  have h := TypedRefinerCharge.charge_eq_sum (fun _ _ : Fin 4 => 1) p E
  simp only [he, sum_const, nsmul_eq_mul] at h
  simpa [TypedRefinerCharge.charge, TypedRefinerCharge.pair, mul_comm] using h

theorem f1_total_count (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges F1 p E) :
    (E.card : ℤ) = f1Base p E + crossCount p E := by
  have htotal := total_edgeVec p E
  rw [edgeVec_f1Matrix p E h] at htotal
  norm_num [f1Matrix, Fin.sum_univ_succ] at htotal
  unfold f1Base crossCount
  omega

theorem f2_total_count (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges F2 p E) :
    (E.card : ℤ) = f2Base p E + crossCount p E := by
  have htotal := total_edgeVec p E
  rw [edgeVec_f2Matrix p E h] at htotal
  norm_num [f2Matrix, Fin.sum_univ_succ] at htotal
  unfold f2Base crossCount
  omega

section ClassParity

variable [Fintype V]

theorem pairVec_class_sum (p : V → Fin 4) (e : Sym2 V) (i j : Fin 4) :
    pairVec p e i j = ∑ v ∈ univ.filter (fun v => p v = i), degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, degContrib, Sym2.lift_mk, sum_add_distrib]
    rw [sum_filter, sum_filter]
    simp only [← ite_and]
    congr 1
    · rw [sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    · rw [sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp

theorem edgeVec_class_sum (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) :
    edgeVec p E i j = ∑ v ∈ univ.filter (fun v => p v = i), degVec p E v j := by
  simp only [edgeVec, degVec, Finset.sum_apply]
  rw [sum_comm]
  exact sum_congr rfl fun e _ => pairVec_class_sum p e i j

theorem class_row_two_dvd (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (heven : ∀ v, Even (incidentLoad E v)) (i : Fin 4) :
    (2 : ℤ) ∣ ∑ j, edgeVec p E i j := by
  simp_rw [edgeVec_class_sum]
  rw [sum_comm]
  apply dvd_sum
  intro v hv
  rw [sum_degVec p E hloop v]
  exact_mod_cast (heven v).two_dvd

theorem f1_class_cut_parities (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F1 p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) :
    (2 : ℤ) ∣ unorderedCount p E 0 2 + unorderedCount p E 0 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 1 2 + unorderedCount p E 1 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 0 2 + unorderedCount p E 1 2 := by
  obtain ⟨k0, hk0⟩ := class_row_two_dvd p E hloop heven 0
  obtain ⟨k1, hk1⟩ := class_row_two_dvd p E hloop heven 1
  obtain ⟨k2, hk2⟩ := class_row_two_dvd p E hloop heven 2
  rw [edgeVec_f1Matrix p E hact] at hk0 hk1 hk2
  norm_num [f1Matrix, Fin.sum_univ_succ] at hk0 hk1 hk2
  exact ⟨⟨k0 - unorderedCount p E 0 0, by omega⟩,
    ⟨k1 - unorderedCount p E 1 1, by omega⟩, ⟨k2 - unorderedCount p E 2 2, by omega⟩⟩

theorem f2_class_cut_parities (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F2 p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) :
    (2 : ℤ) ∣ unorderedCount p E 0 2 + unorderedCount p E 0 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 1 2 + unorderedCount p E 1 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 0 2 + unorderedCount p E 1 2 + unorderedCount p E 2 3 := by
  obtain ⟨k0, hk0⟩ := class_row_two_dvd p E hloop heven 0
  obtain ⟨k1, hk1⟩ := class_row_two_dvd p E hloop heven 1
  obtain ⟨k2, hk2⟩ := class_row_two_dvd p E hloop heven 2
  rw [edgeVec_f2Matrix p E hact] at hk0 hk1 hk2
  norm_num [f2Matrix, Fin.sum_univ_succ] at hk0 hk1 hk2
  exact ⟨⟨k0 - unorderedCount p E 0 0, by omega⟩,
    ⟨k1 - unorderedCount p E 1 1, by omega⟩, ⟨k2, by omega⟩⟩

theorem f2Numerator_even (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F2 p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) : (2 : ℤ) ∣ f2Numerator p E :=
  f2_torsion_numerator_even _ _ _ (f2_class_cut_parities p E hact hloop heven).1

end ClassParity

#print axioms edgeVec_unorderedCount
#print axioms edgeVec_f1Matrix
#print axioms edgeVec_f2Matrix
#print axioms f1FreeCharge_eq_original
#print axioms f2FreeCharge_eq_original
#print axioms unorderedCount_union
#print axioms f2Numerator_union
#print axioms f1_total_count
#print axioms f2_total_count
#print axioms f1_class_cut_parities
#print axioms f2_class_cut_parities
#print axioms f2Numerator_even

end PaddedF12
