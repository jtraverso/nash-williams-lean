/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalBounds

/-! # Bounded real coefficients for the F1/F2 type totals

Diagonal input counts are unordered, as in `ScalarLattice`; the original ordered
diagonal vector is twice this value. No positivity or integral parity is required.
-/

namespace PaddedF12.RealTypeTotals

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks

theorem f1_solve (d0 d1 d2 d3 x02 x03 x12 x13 E : ℝ)
    (hfree : x02 + x03 + x12 + x13 = 2 * (d0 + d1 + d2 + d3))
    (hbound : ∀ z ∈ [d0, d1, d2, d3, x02, x03, x12, x13], |z| ≤ E) :
    ∃ a b c d e f g h : ℝ,
      (d0 = a + b ∧ d1 = c + d ∧ d2 = e + f ∧ d3 = g + h ∧
        x02 = 2 * (a + e) ∧ x03 = 2 * (b + g) ∧
        x12 = 2 * (c + f) ∧ x13 = 2 * (d + h)) ∧
      ∀ z ∈ [a, b, c, d, e, f, g, h], |z| ≤ 8 * E := by
  have h0 := abs_le.mp (hbound d0 (by simp))
  have h1 := abs_le.mp (hbound d1 (by simp))
  have h2 := abs_le.mp (hbound d2 (by simp))
  have h3 := abs_le.mp (hbound d3 (by simp))
  have h02 := abs_le.mp (hbound x02 (by simp))
  have h03 := abs_le.mp (hbound x03 (by simp))
  have h12 := abs_le.mp (hbound x12 (by simp))
  have h13 := abs_le.mp (hbound x13 (by simp))
  have hE : 0 ≤ E := (abs_nonneg d0).trans (hbound d0 (by simp))
  refine ⟨d0, 0, x02 / 2 + x12 / 2 - d2 - d0,
    d1 - (x02 / 2 + x12 / 2 - d2 - d0), x02 / 2 - d0,
    d2 - (x02 / 2 - d0), x03 / 2, d3 - x03 / 2, ?_, ?_⟩
  · (repeat' constructor) <;> linarith
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply abs_le.mpr <;> constructor <;> linarith

theorem f2_solve (d0 d1 x02 x03 x12 x13 x23 E : ℝ)
    (hfree : x02 + x03 + x12 + x13 = 2 * (d0 + d1 + x23))
    (hbound : ∀ z ∈ [d0, d1, x02, x03, x12, x13, x23], |z| ≤ E) :
    ∃ a b c d e f : ℝ,
      (d0 = a + b ∧ d1 = c + d ∧
        x02 = 2 * a + e ∧ x03 = 2 * b + e ∧
        x12 = 2 * c + f ∧ x13 = 2 * d + f ∧ x23 = e + f) ∧
      ∀ z ∈ [a, b, c, d, e, f], |z| ≤ 8 * E := by
  have h0 := abs_le.mp (hbound d0 (by simp))
  have h1 := abs_le.mp (hbound d1 (by simp))
  have h02 := abs_le.mp (hbound x02 (by simp))
  have h03 := abs_le.mp (hbound x03 (by simp))
  have h12 := abs_le.mp (hbound x12 (by simp))
  have h13 := abs_le.mp (hbound x13 (by simp))
  have h23 := abs_le.mp (hbound x23 (by simp))
  have hE : 0 ≤ E := (abs_nonneg d0).trans (hbound d0 (by simp))
  refine ⟨(x02 - x03 + 2 * d0) / 4, d0 - (x02 - x03 + 2 * d0) / 4,
    (x12 - x13 + 2 * d1) / 4, d1 - (x12 - x13 + 2 * d1) / 4,
    x02 - 2 * ((x02 - x03 + 2 * d0) / 4),
    x12 - 2 * ((x12 - x13 + 2 * d1) / 4), ?_, ?_⟩
  · (repeat' constructor) <;> linarith
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply abs_le.mpr <;> constructor <;> linarith

/-- The original ordered edge-vector span has exactly the required free charge. -/
theorem f1_span_free_charge (A : Fin 4 → Fin 4 → ℝ)
    (hspan : ∃ c : Multiset (Fin 4) → ℝ,
      A = ∑ τ ∈ F1, c τ • (fun i j => (typeEdgeVec τ i j : ℝ))) :
    A 0 2 + A 0 3 + A 1 2 + A 1 3 =
      2 * (A 0 0 / 2 + A 1 1 / 2 + A 2 2 / 2 + A 3 3 / 2) := by
  obtain ⟨c, rfl⟩ := hspan
  rw [f1_sum_eq]
  norm_num [Pi.add_apply, Pi.smul_apply, smul_eq_mul, typeEdgeVec]
  ring

/-- The same statement for F2 includes its permitted 23-edge class. -/
theorem f2_span_free_charge (A : Fin 4 → Fin 4 → ℝ)
    (hspan : ∃ c : Multiset (Fin 4) → ℝ,
      A = ∑ τ ∈ F2, c τ • (fun i j => (typeEdgeVec τ i j : ℝ))) :
    A 0 2 + A 0 3 + A 1 2 + A 1 3 =
      2 * (A 0 0 / 2 + A 1 1 / 2 + A 2 3) := by
  obtain ⟨c, rfl⟩ := hspan
  rw [f2_sum_eq]
  norm_num [Pi.add_apply, Pi.smul_apply, smul_eq_mul, typeEdgeVec]
  ring

/-- Integral divisibility supplies a real representation in the original edge-vector span. -/
theorem real_span_of_isIntDiv {V : Type*} [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (E : Finset (Sym2 V))
    (hdiv : IsIntDiv p F E) :
    ∃ c : Multiset (Fin t) → ℝ,
      (fun i j => (edgeVec p E i j : ℝ)) =
        ∑ τ ∈ F, c τ • (fun i j => (typeEdgeVec τ i j : ℝ)) := by
  obtain ⟨c, hc⟩ := hdiv.1
  refine ⟨fun τ => (c τ : ℝ), ?_⟩
  funext i j
  have hij := congrFun (congrFun hc i) j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hij ⊢
  exact_mod_cast hij

#print axioms f1_solve
#print axioms f2_solve
#print axioms f1_span_free_charge
#print axioms f2_span_free_charge
#print axioms real_span_of_isIntDiv

end PaddedF12.RealTypeTotals
