/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalCharge
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.BoundedLattice
import PartitionedTriangleAbsorption.ColouredHub.Lattice

/-!
# Explicit coefficient budgets for the original F1/F2 edge vectors

The coefficient functions below represent the original ordered edge vector.
Their negative mass uses the unchanged `TypedBoundedCoefficients.negativeMass`.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients

theorem f1_sum_eq {M : Type*} [AddCommMonoid M] (g : Multiset (Fin 4) → M) :
    (∑ τ ∈ F1, g τ) =
      g {0, 0, 2} + g {0, 0, 3} + g {1, 1, 2} + g {1, 1, 3} + g {0, 2, 2} + g {1, 2, 2} + g {0, 3, 3} + g {1, 3, 3} := by
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
  simp only [F1, sum_insert h0, sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4, sum_insert h5, sum_insert h6, sum_singleton, add_assoc]

theorem f2_sum_eq {M : Type*} [AddCommMonoid M] (g : Multiset (Fin 4) → M) :
    (∑ τ ∈ F2, g τ) =
      g {0, 0, 2} + g {0, 0, 3} + g {1, 1, 2} + g {1, 1, 3} + g {0, 2, 3} + g {1, 2, 3} := by
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
  simp only [F2, sum_insert h0, sum_insert h1, sum_insert h2, sum_insert h3, sum_insert h4, sum_singleton, add_assoc]

variable {V : Type*} [DecidableEq V]

/-- Explicit original coefficients, each at most `4 K` and total negative mass at most `32 K`. -/
theorem f1_bounded_coefficients (K : ℕ) (p : V → Fin 4) (P : Finset (Sym2 V))
    (hK : P.card ≤ K) (hdiv : IsIntDiv p F1 P) :
    ∃ c : Multiset (Fin 4) → ℤ,
      edgeVec p P = ∑ τ ∈ F1, c τ • typeEdgeVec τ ∧
      negativeMass F1 c ≤ 32 * K ∧ (∀ τ ∈ F1, (c τ).natAbs ≤ 4 * K) := by
  have hact := active_of_isIntDiv TypedTransportExamples.F1_card hdiv
  have hlat := (f1_edge_lattice_iff p P hact).mp hdiv.1
  have hc : ∀ z ∈ [unorderedCount p P 0 0, unorderedCount p P 1 1, unorderedCount p P 2 2, unorderedCount p P 3 3, unorderedCount p P 0 2, unorderedCount p P 0 3, unorderedCount p P 1 2, unorderedCount p P 1 3], 0 ≤ z ∧ z ≤ (K : ℤ) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨unorderedCount_nonneg _ _ _ _,
        (unorderedCount_le_card _ _ _ _).trans (by exact_mod_cast hK)⟩
  obtain ⟨a, b, c, d, e, f, g, h, heq, hb, hm⟩ :=
    f1_bounded_witness K _ _ _ _ _ _ _ _ hc hlat
  refine ⟨f1Coefficients a b c d e f g h, ?_, ?_, ?_⟩
  · rw [edgeVec_f1Matrix p P hact, f1_edge_lattice_matrix, f1Matrix_eq_iff]
    simpa [f1Coefficients] using heq
  · rw [negativeMass, f1_sum_eq]
    simpa [f1Coefficients] using hm
  · intro τ hτ
    simp only [F1, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [f1Coefficients] using hb a (by simp)
    · simpa [f1Coefficients] using hb b (by simp)
    · simpa [f1Coefficients] using hb c (by simp)
    · simpa [f1Coefficients] using hb d (by simp)
    · simpa [f1Coefficients] using hb e (by simp)
    · simpa [f1Coefficients] using hb f (by simp)
    · simpa [f1Coefficients] using hb g (by simp)
    · simpa [f1Coefficients] using hb h (by simp)

/-- Explicit original coefficients, each at most `4 K` and total negative mass at most `32 K`. -/
theorem f2_bounded_coefficients (K : ℕ) (p : V → Fin 4) (P : Finset (Sym2 V))
    (hK : P.card ≤ K) (hdiv : IsIntDiv p F2 P) :
    ∃ c : Multiset (Fin 4) → ℤ,
      edgeVec p P = ∑ τ ∈ F2, c τ • typeEdgeVec τ ∧
      negativeMass F2 c ≤ 32 * K ∧ (∀ τ ∈ F2, (c τ).natAbs ≤ 4 * K) := by
  have hact := active_of_isIntDiv TypedTransportExamples.F2_card hdiv
  have hlat := (f2_edge_lattice_iff p P hact).mp hdiv.1
  have hc : ∀ z ∈ [unorderedCount p P 0 0, unorderedCount p P 1 1, unorderedCount p P 0 2, unorderedCount p P 0 3, unorderedCount p P 1 2, unorderedCount p P 1 3, unorderedCount p P 2 3], 0 ≤ z ∧ z ≤ (K : ℤ) := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨unorderedCount_nonneg _ _ _ _,
        (unorderedCount_le_card _ _ _ _).trans (by exact_mod_cast hK)⟩
  obtain ⟨a, b, c, d, e, f, heq, hb, hm⟩ :=
    f2_bounded_witness K _ _ _ _ _ _ _ hc hlat
  refine ⟨f2Coefficients a b c d e f, ?_, ?_, ?_⟩
  · rw [edgeVec_f2Matrix p P hact, f2_edge_lattice_matrix, f2Matrix_eq_iff]
    simpa [f2Coefficients] using heq
  · rw [negativeMass, f2_sum_eq]
    simpa [f2Coefficients] using hm
  · intro τ hτ
    simp only [F2, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [f2Coefficients] using hb a (by simp)
    · simpa [f2Coefficients] using hb b (by simp)
    · simpa [f2Coefficients] using hb c (by simp)
    · simpa [f2Coefficients] using hb d (by simp)
    · simpa [f2Coefficients] using hb e (by simp)
    · simpa [f2Coefficients] using hb f (by simp)

#print axioms f1_bounded_coefficients
#print axioms f2_bounded_coefficients

end PaddedF12
