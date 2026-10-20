/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalCounts

@[expose] public section

/-!
# The original F1/F2 integer lattice in physical unordered counts

The matrices and scalar lattices in this file are connected by evaluating the
original `typeEdgeVec`, with the diagonal factor of two retained throughout.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse

theorem f1_edge_lattice_matrix (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ F1, c τ • typeEdgeVec τ) =
      f1Matrix (c {0, 0, 2} + c {0, 0, 3}) (c {1, 1, 2} + c {1, 1, 3})
        (c {0, 2, 2} + c {1, 2, 2}) (c {0, 3, 3} + c {1, 3, 3})
        (2 * (c {0, 0, 2} + c {0, 2, 2})) (2 * (c {0, 0, 3} + c {0, 3, 3}))
        (2 * (c {1, 1, 2} + c {1, 2, 2})) (2 * (c {1, 1, 3} + c {1, 3, 3})) := by
  have h0 : ({0, 0, 2} : Multiset (Fin 4)) ∉
      ({{0, 0, 3}, {1, 1, 2}, {1, 1, 3}, {0, 2, 2}, {1, 2, 2}, {0, 3, 3}, {1, 3, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h1 : ({0, 0, 3} : Multiset (Fin 4)) ∉
      ({{1, 1, 2}, {1, 1, 3}, {0, 2, 2}, {1, 2, 2}, {0, 3, 3}, {1, 3, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h2 : ({1, 1, 2} : Multiset (Fin 4)) ∉
      ({{1, 1, 3}, {0, 2, 2}, {1, 2, 2}, {0, 3, 3}, {1, 3, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h3 : ({1, 1, 3} : Multiset (Fin 4)) ∉
      ({{0, 2, 2}, {1, 2, 2}, {0, 3, 3}, {1, 3, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h4 : ({0, 2, 2} : Multiset (Fin 4)) ∉
      ({{1, 2, 2}, {0, 3, 3}, {1, 3, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h5 : ({1, 2, 2} : Multiset (Fin 4)) ∉
      ({{0, 3, 3}, {1, 3, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h6 : ({0, 3, 3} : Multiset (Fin 4)) ∉
      ({{1, 3, 3}} : Finset (Multiset (Fin 4))) := by decide
  simp only [F1, sum_insert h0, sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4, sum_insert h5, sum_insert h6, sum_singleton]
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [f1Matrix, typeEdgeVec] <;> ring

theorem f2_edge_lattice_matrix (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ F2, c τ • typeEdgeVec τ) =
      f2Matrix (c {0, 0, 2} + c {0, 0, 3}) (c {1, 1, 2} + c {1, 1, 3})
        (2 * c {0, 0, 2} + c {0, 2, 3}) (2 * c {0, 0, 3} + c {0, 2, 3})
        (2 * c {1, 1, 2} + c {1, 2, 3}) (2 * c {1, 1, 3} + c {1, 2, 3})
        (c {0, 2, 3} + c {1, 2, 3}) := by
  have h0 : ({0, 0, 2} : Multiset (Fin 4)) ∉
      ({{0, 0, 3}, {1, 1, 2}, {1, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h1 : ({0, 0, 3} : Multiset (Fin 4)) ∉
      ({{1, 1, 2}, {1, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h2 : ({1, 1, 2} : Multiset (Fin 4)) ∉
      ({{1, 1, 3}, {0, 2, 3}, {1, 2, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h3 : ({1, 1, 3} : Multiset (Fin 4)) ∉
      ({{0, 2, 3}, {1, 2, 3}} : Finset (Multiset (Fin 4))) := by decide
  have h4 : ({0, 2, 3} : Multiset (Fin 4)) ∉
      ({{1, 2, 3}} : Finset (Multiset (Fin 4))) := by decide
  simp only [F2, sum_insert h0, sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4, sum_singleton]
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [f2Matrix, typeEdgeVec] <;> ring

theorem f1Matrix_eq_iff (d0 d1 d2 d3 x02 x03 x12 x13 d0' d1' d2' d3' x02' x03' x12' x13' : ℤ) :
    f1Matrix d0 d1 d2 d3 x02 x03 x12 x13 = f1Matrix d0' d1' d2' d3' x02' x03' x12' x13' ↔
      d0 = d0' ∧ d1 = d1' ∧ d2 = d2' ∧ d3 = d3' ∧ x02 = x02' ∧ x03 = x03' ∧ x12 = x12' ∧ x13 = x13' := by
  constructor
  · intro h
    have h0 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 0 0) h
    have h1 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 1 1) h
    have h2 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 2 2) h
    have h3 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 3 3) h
    have h4 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 0 2) h
    have h5 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 0 3) h
    have h6 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 1 2) h
    have h7 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 1 3) h
    norm_num [f1Matrix] at h0 h1 h2 h3 h4 h5 h6 h7
    omega
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem f2Matrix_eq_iff (d0 d1 x02 x03 x12 x13 x23 d0' d1' x02' x03' x12' x13' x23' : ℤ) :
    f2Matrix d0 d1 x02 x03 x12 x13 x23 = f2Matrix d0' d1' x02' x03' x12' x13' x23' ↔
      d0 = d0' ∧ d1 = d1' ∧ x02 = x02' ∧ x03 = x03' ∧ x12 = x12' ∧ x13 = x13' ∧ x23 = x23' := by
  constructor
  · intro h
    have h0 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 0 0) h
    have h1 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 1 1) h
    have h2 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 0 2) h
    have h3 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 0 3) h
    have h4 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 1 2) h
    have h5 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 1 3) h
    have h6 := congrArg (fun M : Fin 4 → Fin 4 → ℤ => M 2 3) h
    norm_num [f2Matrix] at h0 h1 h2 h3 h4 h5 h6
    omega
  · rintro ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rfl

/-- A coefficient function with the specified values on the eight F1 types. -/
def f1Coefficients (a b c d e f g h : ℤ) (τ : Multiset (Fin 4)) : ℤ :=
  if τ.count 0 = 2 then (if τ.count 2 = 1 then a else b) else
  if τ.count 1 = 2 then (if τ.count 2 = 1 then c else d) else
  if τ.count 2 = 2 then (if τ.count 0 = 1 then e else f) else
  if τ.count 0 = 1 then g else h

/-- A coefficient function with the specified values on the six F2 types. -/
def f2Coefficients (a b c d e f : ℤ) (τ : Multiset (Fin 4)) : ℤ :=
  if τ.count 0 = 2 then (if τ.count 2 = 1 then a else b) else
  if τ.count 1 = 2 then (if τ.count 2 = 1 then c else d) else
  if τ.count 0 = 1 then e else f

theorem f1_matrix_lattice_iff (d0 d1 d2 d3 x02 x03 x12 x13 : ℤ) :
    (∃ c : Multiset (Fin 4) → ℤ,
      f1Matrix d0 d1 d2 d3 x02 x03 x12 x13 = ∑ τ ∈ F1, c τ • typeEdgeVec τ) ↔
      F1Lattice d0 d1 d2 d3 x02 x03 x12 x13 := by
  constructor
  · rintro ⟨c, hc⟩
    rw [f1_edge_lattice_matrix, f1Matrix_eq_iff] at hc
    exact ⟨c {0, 0, 2}, c {0, 0, 3}, c {1, 1, 2}, c {1, 1, 3},
      c {0, 2, 2}, c {1, 2, 2}, c {0, 3, 3}, c {1, 3, 3}, hc⟩
  · rintro ⟨a, b, c, d, e, f, g, h, hc⟩
    refine ⟨f1Coefficients a b c d e f g h, ?_⟩
    rw [f1_edge_lattice_matrix, f1Matrix_eq_iff]
    simpa [f1Coefficients] using hc

theorem f2_matrix_lattice_iff (d0 d1 x02 x03 x12 x13 x23 : ℤ) :
    (∃ c : Multiset (Fin 4) → ℤ,
      f2Matrix d0 d1 x02 x03 x12 x13 x23 = ∑ τ ∈ F2, c τ • typeEdgeVec τ) ↔
      F2Lattice d0 d1 x02 x03 x12 x13 x23 := by
  constructor
  · rintro ⟨c, hc⟩
    rw [f2_edge_lattice_matrix, f2Matrix_eq_iff] at hc
    exact ⟨c {0, 0, 2}, c {0, 0, 3}, c {1, 1, 2}, c {1, 1, 3},
      c {0, 2, 3}, c {1, 2, 3}, hc⟩
  · rintro ⟨a, b, c, d, e, f, hc⟩
    refine ⟨f2Coefficients a b c d e f, ?_⟩
    rw [f2_edge_lattice_matrix, f2Matrix_eq_iff]
    simpa [f2Coefficients] using hc

variable {V : Type*} [DecidableEq V]

theorem f1_edge_lattice_iff (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F1 p E) :
    (∃ c : Multiset (Fin 4) → ℤ, edgeVec p E = ∑ τ ∈ F1, c τ • typeEdgeVec τ) ↔
      F1Lattice (unorderedCount p E 0 0) (unorderedCount p E 1 1)
        (unorderedCount p E 2 2) (unorderedCount p E 3 3)
        (unorderedCount p E 0 2) (unorderedCount p E 0 3)
        (unorderedCount p E 1 2) (unorderedCount p E 1 3) := by
  rw [edgeVec_f1Matrix p E hact, f1_matrix_lattice_iff]

theorem f2_edge_lattice_iff (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges F2 p E) :
    (∃ c : Multiset (Fin 4) → ℤ, edgeVec p E = ∑ τ ∈ F2, c τ • typeEdgeVec τ) ↔
      F2Lattice (unorderedCount p E 0 0) (unorderedCount p E 1 1)
        (unorderedCount p E 0 2) (unorderedCount p E 0 3)
        (unorderedCount p E 1 2) (unorderedCount p E 1 3) (unorderedCount p E 2 3) := by
  rw [edgeVec_f2Matrix p E hact, f2_matrix_lattice_iff]

/-- F1 divisibility is exactly even degree, zero free charge and one parity bit. -/
theorem isIntDiv_F1_iff_counts [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F1 p E) :
    IsIntDiv p F1 E ↔ (∀ v, Even (incidentLoad E v)) ∧
      f1FreeCharge p E = 0 ∧ (2 : ℤ) ∣ unorderedCount p E 0 2 := by
  constructor
  · intro hd
    obtain ⟨_, heven, hedge⟩ := (TypedPieceConditions.F1_isIntDiv_iff hloop).mp hd
    have hl := (f1_edge_lattice_iff p E hact).mp hedge
    have hb := (f1_lattice_iff _ _ _ _ _ _ _ _).mp hl
    refine ⟨heven, ?_, hb.2.1⟩
    rw [f1FreeCharge_eq_original p E hact]
    exact TypedRefinerCharge.charge_eq_zero_of_isIntDiv TypedRefinerCharge.kills_chi1 hd
  · rintro ⟨heven, hcharge, hbit⟩
    refine (TypedPieceConditions.F1_isIntDiv_iff hloop).mpr ⟨hact, heven, ?_⟩
    rw [f1_edge_lattice_iff p E hact]
    obtain ⟨hr0, hr1, hr2⟩ := f1_class_cut_parities p E hact hloop heven
    rw [f1_lattice_iff_one_bit _ _ _ _ _ _ _ _ hr0 hr1 hr2]
    exact ⟨(freeCharge_zero_iff _ _).mp hcharge, hbit⟩

/-- F2 has one normalized mod-four obstruction in addition to its free charge. -/
theorem isIntDiv_F2_iff_counts [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F2 p E) :
    IsIntDiv p F2 E ↔ (∀ v, Even (incidentLoad E v)) ∧
      f2FreeCharge p E = 0 ∧ (4 : ℤ) ∣ f2Numerator p E := by
  constructor
  · intro hd
    obtain ⟨_, heven, hedge⟩ := (TypedPieceConditions.F2_isIntDiv_iff hloop).mp hd
    have hl := (f2_edge_lattice_iff p E hact).mp hedge
    have hb := (f2_lattice_iff _ _ _ _ _ _ _).mp hl
    refine ⟨heven, ?_, hb.2.1⟩
    rw [f2FreeCharge_eq_original p E hact]
    exact TypedRefinerCharge.charge_eq_zero_of_isIntDiv TypedRefinerCharge.kills_chi2 hd
  · rintro ⟨heven, hcharge, hbit⟩
    refine (TypedPieceConditions.F2_isIntDiv_iff hloop).mpr ⟨hact, heven, ?_⟩
    rw [f2_edge_lattice_iff p E hact]
    obtain ⟨_, _, hr2⟩ := f2_class_cut_parities p E hact hloop heven
    rw [f2_lattice_iff_one_bit _ _ _ _ _ _ _ hr2]
    exact ⟨(freeCharge_zero_iff _ _).mp hcharge, hbit⟩

/-- The F1 criterion with the original matrix charge. -/
theorem isIntDiv_F1_iff_charge_torsion [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F1 p E) :
    IsIntDiv p F1 E ↔ (∀ v, Even (incidentLoad E v)) ∧
      TypedRefinerCharge.charge TypedRefinerCharge.chi1 p E = 0 ∧
      (2 : ℤ) ∣ unorderedCount p E 0 2 := by
  rw [← f1FreeCharge_eq_original p E hact, isIntDiv_F1_iff_counts p E hloop hact]

/-- The F2 criterion with the original matrix charge. -/
theorem isIntDiv_F2_iff_charge_torsion [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hact : ActiveEdges F2 p E) :
    IsIntDiv p F2 E ↔ (∀ v, Even (incidentLoad E v)) ∧
      TypedRefinerCharge.charge TypedRefinerCharge.chi2 p E = 0 ∧
      (4 : ℤ) ∣ f2Numerator p E := by
  rw [← f2FreeCharge_eq_original p E hact, isIntDiv_F2_iff_counts p E hloop hact]

#print axioms isIntDiv_F1_iff_counts
#print axioms isIntDiv_F2_iff_counts
#print axioms isIntDiv_F1_iff_charge_torsion
#print axioms isIntDiv_F2_iff_charge_torsion

#print axioms f1_matrix_lattice_iff
#print axioms f2_matrix_lattice_iff
#print axioms f1_edge_lattice_iff
#print axioms f2_edge_lattice_iff

#print axioms f1_edge_lattice_matrix
#print axioms f2_edge_lattice_matrix

end PaddedF12
