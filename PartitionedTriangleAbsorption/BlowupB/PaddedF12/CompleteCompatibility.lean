/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.CompleteCopyInverse

@[expose] public section

/-! # Compatibility of original divisible edge sets minus typed triangle boundaries -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks
open PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

def edgeIndicator (E : Finset (Sym2 V)) (e : Sym2 V) : ℝ := if e ∈ E then 1 else 0

/- These counting identities use the original ordered `pairVec` convention. -/
theorem pairVec_eq_class_degree (p : V → Fin 4) (e : Sym2 V) (i j : Fin 4) :
    pairVec p e i j = ∑ v ∈ classVertices p i, degContrib p v e j := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, degContrib, Sym2.lift_mk, sum_add_distrib]
    rw [show classVertices p i = univ.filter (fun v => p v = i) by rfl]
    rw [sum_filter, sum_filter]
    simp only [← ite_and]
    congr 1
    · rw [sum_eq_single a (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp
    · rw [sum_eq_single b (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
      simp

theorem edgeVec_eq_class_degree (p : V → Fin 4) (E : Finset (Sym2 V)) (i j : Fin 4) :
    edgeVec p E i j = ∑ v ∈ classVertices p i, degVec p E v j := by
  simp only [edgeVec, degVec, Finset.sum_apply]
  rw [sum_comm]
  exact sum_congr rfl (fun e _ => pairVec_eq_class_degree p e i j)

theorem class_degree_graph_count (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (j : Fin 4) :
    degVec p G.edgeFinset a j = ((univ.filter (fun b => G.Adj a b ∧ p b = j)).card : ℤ) := by
  let W := univ.filter (fun b => G.Adj a b ∧ p b = j)
  have himg : W.image (fun b => s(a, b)) ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨b, hb, rfl⟩ := mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (mem_filter.mp hb).2.1
  have hinj : Set.InjOn (fun b => s(a, b)) W := by
    intro b _ b' _ h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  rw [degVec, Finset.sum_apply, ← sum_subset himg, sum_image hinj, card_eq_sum_ones, Nat.cast_sum]
  · apply sum_congr rfl
    intro b hb
    have hb' := (mem_filter.mp hb).2
    have hba : b ≠ a := (G.ne_of_adj hb'.1).symm
    simp [degContrib, hb'.2, hba]
  · intro e he hne
    induction e using Sym2.ind with
    | _ b c =>
      have hbc : G.Adj b c := SimpleGraph.mem_edgeFinset.mp he
      simp only [degContrib, Sym2.lift_mk]
      have h1 : ¬ (b = a ∧ p c = j) := by
        rintro ⟨rfl, hc⟩
        exact hne (mem_image.mpr ⟨c, mem_filter.mpr ⟨mem_univ _, hbc, hc⟩, rfl⟩)
      have h2 : ¬ (c = a ∧ p b = j) := by
        rintro ⟨rfl, hb⟩
        exact hne (mem_image.mpr ⟨b, mem_filter.mpr ⟨mem_univ _, hbc.symm, hb⟩,
          Sym2.eq_swap⟩)
      simp [h1, h2]

theorem classRow_graph_indicator (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (j : Fin 4) :
    classRow p (fun a b => if G.Adj a b then 1 else 0) a j =
      (degVec p G.edgeFinset a j : ℝ) := by
  rw [class_degree_graph_count]
  simp only [classRow, classVertices, card_eq_sum_ones,
    Nat.cast_sum, Int.cast_sum, Nat.cast_ite, Int.cast_ite,
    Nat.cast_one, Nat.cast_zero, Int.cast_one, Int.cast_zero, sum_filter]
  apply sum_congr rfl
  intro b _
  by_cases hb : p b = j <;> by_cases hab : G.Adj a b <;> simp [hb, hab]

theorem classTotal_graph_indicator (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] :
    classTotal p (fun a b => if G.Adj a b then 1 else 0) =
      fun i j => (edgeVec p G.edgeFinset i j : ℝ) := by
  funext i j
  rw [edgeVec_eq_class_degree]
  simp only [Int.cast_sum]
  exact sum_congr rfl (fun a _ => classRow_graph_indicator p G a j)

theorem classTotal_edgeIndicator (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    classTotal p (fun a b => edgeIndicator E s(a, b)) =
      fun i j => (edgeVec p E i j : ℝ) := by
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
  have h := classTotal_graph_indicator p G
  simp_rw [hG] at h
  rw [hGE] at h
  exact h

theorem classTotal_boundary (p : V → Fin 4) (z : TriangleChain V) (i j : Fin 4) :
    classTotal p (fun a b => boundary z s(a, b)) i j =
      ∑ T : Finset V, z T * (edgeVec p (triEdges T) i j : ℝ) := by
  calc
    _ = ∑ a ∈ classVertices p i, ∑ T : Finset V,
        ∑ b ∈ classVertices p j, z T * (if s(a, b) ∈ triEdges T then 1 else 0) := by
      unfold classTotal classRow boundary
      apply sum_congr rfl
      intro a _
      exact sum_comm
    _ = ∑ T : Finset V, ∑ a ∈ classVertices p i,
        ∑ b ∈ classVertices p j, z T * (if s(a, b) ∈ triEdges T then 1 else 0) := sum_comm
    _ = ∑ T : Finset V, z T * classTotal p (fun a b => edgeIndicator (triEdges T) s(a, b)) i j := by
      simp only [classTotal, classRow, edgeIndicator, mul_sum]
    _ = _ := by
      apply sum_congr rfl
      intro T _
      rw [classTotal_edgeIndicator p (triEdges T) (fun e he => (mem_filter.mp he).2)]

theorem real_span_boundary (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) (z : TriangleChain V) (hz : CopySupported p F G z) :
    ∃ c : Multiset (Fin 4) → ℝ,
      classTotal p (fun a b => boundary z s(a, b)) =
        ∑ τ ∈ F, c τ • (fun i j => (typeEdgeVec τ i j : ℝ)) := by
  classical
  refine ⟨fun τ => ∑ T : Finset V with triType p T = τ, z T, ?_⟩
  funext i j
  rw [classTotal_boundary]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sum_mul,
    sum_filter, ite_mul, zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro T _
  by_cases hT : IsCopy p F G T
  · rw [edgeVec_triEdges p hT.1.card_eq]
    have ht : triType p T ∈ F := hT.2
    rw [sum_eq_single (triType p T)]
    · simp
    · intro τ _ hτ
      simp only [Ne.symm hτ, ite_false]
    · exact fun hnot => False.elim (hnot ht)
  · rw [hz T hT]
    simp only [zero_mul, ite_self, sum_const_zero]

theorem F1RealCompatible.indicator_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F1 E) :
    F1RealCompatible p (fun a b => edgeIndicator E s(a, b)) := by
  apply F1RealCompatible.of_span
  rw [classTotal_edgeIndicator p E hloop]
  exact PaddedF12.RealTypeTotals.real_span_of_isIntDiv p F1 E hdiv

theorem F2RealCompatible.indicator_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F2 E) :
    F2RealCompatible p (fun a b => edgeIndicator E s(a, b)) := by
  apply F2RealCompatible.of_span
  rw [classTotal_edgeIndicator p E hloop]
  exact PaddedF12.RealTypeTotals.real_span_of_isIntDiv p F2 E hdiv

theorem F1RealCompatible.of_boundary (p : V → Fin 4) (G : SimpleGraph V)
    (z : TriangleChain V) (hz : CopySupported p F1 G z) :
    F1RealCompatible p (fun a b => boundary z s(a, b)) :=
  F1RealCompatible.of_span p _ (real_span_boundary p F1 G z hz)

theorem F2RealCompatible.of_boundary (p : V → Fin 4) (G : SimpleGraph V)
    (z : TriangleChain V) (hz : CopySupported p F2 G z) :
    F2RealCompatible p (fun a b => boundary z s(a, b)) :=
  F2RealCompatible.of_span p _ (real_span_boundary p F2 G z hz)

theorem F1RealCompatible.sub {p : V → Fin 4} {g h : V → V → ℝ}
    (hg : F1RealCompatible p g) (hh : F1RealCompatible p h) :
    F1RealCompatible p (fun a b => g a b - h a b) := by
  unfold F1RealCompatible at *
  simp only [classTotal_sub]
  linarith

theorem F2RealCompatible.sub {p : V → Fin 4} {g h : V → V → ℝ}
    (hg : F2RealCompatible p g) (hh : F2RealCompatible p h) :
    F2RealCompatible p (fun a b => g a b - h a b) := by
  unfold F2RealCompatible at *
  simp only [classTotal_sub]
  linarith

theorem F1RealCompatible.residual_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F1 E) (G : SimpleGraph V)
    (z : TriangleChain V) (hz : CopySupported p F1 G z) :
    F1RealCompatible p (fun a b => edgeIndicator E s(a, b) - boundary z s(a, b)) :=
  (F1RealCompatible.indicator_of_isIntDiv p E hloop hdiv).sub
    (F1RealCompatible.of_boundary p G z hz)

theorem F2RealCompatible.residual_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F2 E) (G : SimpleGraph V)
    (z : TriangleChain V) (hz : CopySupported p F2 G z) :
    F2RealCompatible p (fun a b => edgeIndicator E s(a, b) - boundary z s(a, b)) :=
  (F2RealCompatible.indicator_of_isIntDiv p E hloop hdiv).sub
    (F2RealCompatible.of_boundary p G z hz)

#print axioms classTotal_edgeIndicator
#print axioms classTotal_boundary
#print axioms real_span_boundary
#print axioms F1RealCompatible.residual_of_isIntDiv
#print axioms F2RealCompatible.residual_of_isIntDiv

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
