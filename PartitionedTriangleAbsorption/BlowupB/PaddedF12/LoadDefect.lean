/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.CompleteCompatibility

/-! # The supported load defect used in the final host repair -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks
open PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

def loadDefect (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V) (e : Sym2 V) : ℝ :=
  if e ∈ G.edgeFinset then
    1 - ∑ T ∈ copies p F G with e ∈ triEdges T, φ T else 0

theorem loadDefect_zero (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V)
    (e : Sym2 V) (he : e ∉ G.edgeFinset) : loadDefect p F G φ e = 0 := by
  simp only [loadDefect, he, ite_false]

theorem copy_load_zero_of_not_edge (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V)
    (e : Sym2 V) (he : e ∉ G.edgeFinset) :
    (∑ T ∈ copies p F G with e ∈ triEdges T, φ T) = 0 := by
  apply sum_eq_zero
  intro T hT
  obtain ⟨hc, heT⟩ := mem_filter.mp hT
  exact False.elim (he (triEdges_subset_of_isCopy (mem_copies_iff.mp hc) heT))

theorem loadDefect_eq_indicator_sub_boundary (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : TriangleChain V) :
    loadDefect p F G φ = fun e => edgeIndicator G.edgeFinset e - boundary (copyRestriction p F G φ) e := by
  funext e
  rw [copyRestriction_boundary]
  by_cases he : e ∈ G.edgeFinset
  · simp only [loadDefect, edgeIndicator, he, ite_true]
  · simp only [loadDefect, edgeIndicator, he, ite_false,
      copy_load_zero_of_not_edge p F G φ e he, sub_self]

theorem loadDefect_bound (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V) (ε : ℝ)
    (hε : 0 ≤ ε)
    (hloads : ∀ e ∈ G.edgeFinset, |1 - ∑ T ∈ copies p F G with e ∈ triEdges T, φ T| ≤ ε)
    (e : Sym2 V) : |loadDefect p F G φ e| ≤ ε := by
  by_cases he : e ∈ G.edgeFinset
  · simpa only [loadDefect, he, ite_true] using hloads e he
  · simpa only [loadDefect, he, ite_false, abs_zero] using hε

theorem loadDefect_supported (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V)
    (hG : G ≤ activeCompleteGraph p F) : Sym2DemandSupported p F (loadDefect p F G φ) := by
  intro e he
  apply loadDefect_zero
  intro heG
  induction e using Sym2.ind with
  | _ a b =>
    exact he (SimpleGraph.mem_edgeFinset.mpr (hG (SimpleGraph.mem_edgeFinset.mp heG)))

theorem loadDefect_supported_of_allowed (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) :
    Sym2DemandSupported p F (loadDefect p F G φ) := by
  apply loadDefect_supported p F G φ
  intro a b hab
  exact ⟨hab.ne, hG a b hab⟩

theorem loadDefect_family (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V)
    (hF : F = F1 ∨ F = F2) (hdiv : IsIntDiv p F G.edgeFinset) :
    (F = F1 ∧ F1RealCompatible p (fun a b => loadDefect p F G φ s(a, b))) ∨
      (F = F2 ∧ F2RealCompatible p (fun a b => loadDefect p F G φ s(a, b))) := by
  have hloop : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag :=
    fun _ he => G.not_isDiag_of_mem_edgeFinset he
  rcases hF with rfl | rfl
  · apply Or.inl
    refine ⟨rfl, ?_⟩
    rw [loadDefect_eq_indicator_sub_boundary]
    exact F1RealCompatible.residual_of_isIntDiv p G.edgeFinset hloop hdiv G
      (copyRestriction p F1 G φ) (copyRestriction_supported p F1 G φ)
  · apply Or.inr
    refine ⟨rfl, ?_⟩
    rw [loadDefect_eq_indicator_sub_boundary]
    exact F2RealCompatible.residual_of_isIntDiv p G.edgeFinset hloop hdiv G
      (copyRestriction p F2 G φ) (copyRestriction_supported p F2 G φ)

#print axioms loadDefect_eq_indicator_sub_boundary
#print axioms loadDefect_supported
#print axioms loadDefect_family

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
