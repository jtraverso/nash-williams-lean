/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.Reduction

/-! # Local real compatibility of the actual repair defect

Global type totals alone are not sufficient for a general complete inverse.
This module adds the root profiles already supplied by integral divisibility.
It does not assert existence of a bounded inverse for arbitrary families.
-/

noncomputable section

namespace PaddedGeneral

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The profile at each physical root lies in the real span of its allowed links.
Repeated labels are counted with their original `typeDegVec` multiplicities. -/
def LocalSpanCompat (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (r : Sym2 V → ℝ) : Prop :=
  ∀ v, ∃ c : Multiset (Fin 4) → ℝ,
    classRow p (fun a b => r s(a, b)) v =
      ∑ τ ∈ F with p v ∈ τ, c τ • (fun j => (typeDegVec τ (p v) j : ℝ))

def FullSpanCompat (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (r : Sym2 V → ℝ) : Prop := SpanCompat p F r ∧ LocalSpanCompat p F r

theorem classRow_edgeIndicator (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (v : V) (j : Fin 4) :
    classRow p (fun a b => edgeIndicator E s(a, b)) v j = (degVec p E v j : ℝ) := by
  classical
  let G := SimpleGraph.fromEdgeSet (E : Set (Sym2 V))
  have hGE (inst : Fintype G.edgeSet) : @SimpleGraph.edgeFinset V G inst = E := by
    ext e
    simp only [G, SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_fromEdgeSet,
      Set.mem_sdiff, mem_coe, Sym2.mem_diagSet]
    exact ⟨And.left, fun he => ⟨he, hloop e he⟩⟩
  have hG (a b : V) : G.Adj a b ↔ s(a, b) ∈ E := by
    change (s(a, b) ∈ E ∧ a ≠ b) ↔ s(a, b) ∈ E
    refine ⟨And.left, fun he => ⟨he, ?_⟩⟩
    intro hab
    subst b
    exact hloop _ he (by simp)
  have h := classRow_graph_indicator p G v j
  simp_rw [hG] at h
  rw [hGE] at h
  exact h

theorem localSpan_indicator_of_isIntDiv (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F E) :
    LocalSpanCompat p F (edgeIndicator E) := by
  intro v
  obtain ⟨c, hc⟩ := hdiv.2 v
  refine ⟨fun τ => (c τ : ℝ), ?_⟩
  funext j
  rw [classRow_edgeIndicator p E hloop]
  have hj := congrFun hc j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
  exact_mod_cast hj

theorem classRow_boundary (p : V → Fin 4) (z : TriangleChain V) (v : V) (j : Fin 4) :
    classRow p (fun a b => boundary z s(a, b)) v j =
      ∑ T : Finset V, z T * (degVec p (triEdges T) v j : ℝ) := by
  calc
    _ = ∑ T : Finset V, ∑ b ∈ classVertices p j,
        z T * (if s(v, b) ∈ triEdges T then 1 else 0) := by
      unfold classRow boundary
      exact sum_comm
    _ = ∑ T : Finset V,
        z T * classRow p (fun a b => edgeIndicator (triEdges T) s(a, b)) v j := by
      simp only [classRow, edgeIndicator, mul_sum]
    _ = _ := by
      apply sum_congr rfl
      intro T _
      rw [classRow_edgeIndicator p (triEdges T) (fun e he => (mem_filter.mp he).2)]

theorem localSpan_boundary (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) (z : TriangleChain V) (hz : CopySupported p F G z) :
    LocalSpanCompat p F (boundary z) := by
  classical
  intro v
  refine ⟨fun τ => ∑ T : Finset V, if v ∈ T ∧ triType p T = τ then z T else 0, ?_⟩
  funext j
  rw [classRow_boundary]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul,
    ite_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  by_cases hT : IsCopy p F G T
  · rw [degVec_triEdges p hT.1.card_eq]
    by_cases hv : v ∈ T
    · have hp : p v ∈ triType p T := by
        exact Multiset.mem_map.mpr ⟨v, hv, rfl⟩
      rw [ite_eq_left hv]
      rw [sum_eq_single (triType p T)]
      · simp [hv]
      · intro τ _ hτ
        simp [Ne.symm hτ]
      · exact fun hnot => False.elim (hnot (mem_filter.mpr ⟨hT.2, hp⟩))
    · simp [hv]
  · rw [hz T hT]
    simp

omit [DecidableEq V] in
theorem LocalSpanCompat.sub {p : V → Fin 4} {F : Finset (Multiset (Fin 4))}
    {r s : Sym2 V → ℝ} (hr : LocalSpanCompat p F r) (hs : LocalSpanCompat p F s) :
    LocalSpanCompat p F (fun e => r e - s e) := by
  intro v
  obtain ⟨c, hc⟩ := hr v
  obtain ⟨d, hd⟩ := hs v
  refine ⟨fun τ => c τ - d τ, ?_⟩
  funext j
  have h1 := congrFun hc j
  have h2 := congrFun hd j
  simp only [classRow, sum_sub_distrib] at h1 h2 ⊢
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul,
    sum_sub_distrib] at h1 h2 ⊢
  rw [h1, h2]

/-- No accuracy, positivity or size premise is needed for local compatibility. -/
theorem loadDefect_localSpan (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V)
    (hdiv : IsIntDiv p F G.edgeFinset) :
    LocalSpanCompat p F (loadDefect p F G φ) := by
  rw [loadDefect_eq_indicator_sub_boundary]
  exact (localSpan_indicator_of_isIntDiv p F G.edgeFinset
    (fun _ he => G.not_isDiag_of_mem_edgeFinset he) hdiv).sub
      (localSpan_boundary p F G (copyRestriction p F G φ)
        (copyRestriction_supported p F G φ))

theorem loadDefect_fullSpan (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (φ : TriangleChain V)
    (hdiv : IsIntDiv p F G.edgeFinset) :
    FullSpanCompat p F (loadDefect p F G φ) :=
  ⟨loadDefect_span p F G φ hdiv, loadDefect_localSpan p F G φ hdiv⟩

#print axioms localSpan_indicator_of_isIntDiv
#print axioms localSpan_boundary
#print axioms loadDefect_localSpan
#print axioms loadDefect_fullSpan

end PaddedGeneral
