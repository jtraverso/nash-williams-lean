/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.NonextremeKept

/-! # Monotonicity and sparse edge deletion on the original vertex type -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply AntiEdgeSelection TypedApplicationLinks
open StructuralF3General.FiniteLibrary

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem Nonextreme.mono {G : SimpleGraph V} [DecidableRel G.Adj] {D : Finset V}
    {a b : ℝ} (h : Nonextreme G D a) (hba : b ≤ a) : Nonextreme G D b := by
  intro X hX hbal
  have hh := mul_le_mul_of_nonneg_right hba (sq_nonneg (D.card:ℝ))
  obtain ⟨hb,hc⟩ := h X hX hbal
  exact ⟨hh.trans_lt hb,hh.trans_lt hc⟩

theorem HostHyp.mono {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b ε ε' : ℝ} (h : HostHyp p G a ε) (hba : b ≤ a) (he : ε ≤ ε') :
    HostHyp p G b ε' := by
  have hn : (0:ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hem := mul_le_mul_of_nonneg_right he hn
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i; have := h.part_size i; nlinarith
  · intro v; have := h.internal_lower v; nlinarith
  · intro v; have := h.internal_upper v; nlinarith
  · intro v; have := h.cross_lower v; nlinarith
  · obtain ⟨i,hi⟩ := h.good_part
    exact ⟨i,hi.mono hba⟩

theorem partDeg_delete_bounds (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (i : Fin 2) (v : V) :
    partDeg p (G.deleteEdges (B:Set (Sym2 V))) i v ≤ partDeg p G i v ∧
      partDeg p G i v ≤ partDeg p (G.deleteEdges (B:Set (Sym2 V))) i v + incidentLoad B v := by
  classical
  have hn : partNbrs p (G.deleteEdges (B:Set (Sym2 V))) i v =
      partNbrs p G i v \ removedNbrs B v := by
    ext w
    simp only [mem_partNbrs, SimpleGraph.deleteEdges_adj, mem_sdiff,
      removedNbrs,mem_filter,mem_univ,true_and,mem_coe]
    tauto
  unfold partDeg
  rw [hn]
  refine ⟨card_le_card sdiff_subset,?_⟩
  have hcard := card_sdiff_add_card_inter (partNbrs p G i v) (removedNbrs B v)
  have hsub : (partNbrs p G i v ∩ removedNbrs B v).card ≤ incidentLoad B v :=
    (card_le_card inter_subset_right).trans (removedNbrs_card B v)
  omega

theorem HostHyp.delete
    {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {a ε δ : ℝ} (h : HostHyp p G (2*a) ε)
    (ha : 0 ≤ a) (hε1 : ε ≤ 1/3) (hδ : 0 ≤ δ) (hδa : δ ≤ a/100)
    (B : Finset (Sym2 V)) (hB : DegBounded B (δ*Fintype.card V)) :
    HostHyp p (G.deleteEdges (B:Set (Sym2 V))) a (ε+δ) := by
  classical
  let n : ℝ := Fintype.card V
  have hn : 0 ≤ n := Nat.cast_nonneg _
  have hδn : 0 ≤ δ*n := mul_nonneg hδ hn
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i
    have hs := h.part_size i
    change (1-ε)*n/2 ≤ _ at hs
    change (1-(ε+δ))*n/2 ≤ _
    nlinarith
  · intro v
    have hs := h.internal_lower v
    have hb := hB v
    have hl : (partDeg p G (p v) v : ℝ) ≤
        partDeg p (G.deleteEdges (B:Set (Sym2 V))) (p v) v + incidentLoad B v := by
      exact_mod_cast (partDeg_delete_bounds p G B (p v) v).2
    change (1/4-ε)*n ≤ _ at hs
    change (incidentLoad B v:ℝ) ≤ δ*n at hb
    change (1/4-(ε+δ))*n ≤ _
    nlinarith
  · intro v
    have hs := h.internal_upper v
    have hu : (partDeg p (G.deleteEdges (B:Set (Sym2 V))) (p v) v:ℝ) ≤
        partDeg p G (p v) v := by exact_mod_cast (partDeg_delete_bounds p G B (p v) v).1
    change _ ≤ (1/4+ε)*n at hs
    change _ ≤ (1/4+(ε+δ))*n
    nlinarith
  · intro v
    have hs := h.cross_lower v
    have hb := hB v
    have hl : (partDeg p G (other0 (p v)) v : ℝ) ≤
        partDeg p (G.deleteEdges (B:Set (Sym2 V))) (other0 (p v)) v + incidentLoad B v := by
      exact_mod_cast (partDeg_delete_bounds p G B (other0 (p v)) v).2
    change (1/2-ε)*n ≤ _ at hs
    change (incidentLoad B v:ℝ) ≤ δ*n at hb
    change (1/2-(ε+δ))*n ≤ _
    nlinarith
  · obtain ⟨i,hi⟩ := h.good_part
    refine ⟨i,hi.restrict_delete ha (Subset.refl _) B ?_⟩
    simp only [sdiff_self, Finset.bot_eq_empty, card_empty,Nat.cast_zero,zero_mul,zero_add]
    let d : ℝ := (partSet p i).card
    have hd : 0 ≤ d := Nat.cast_nonneg _
    have hdge : n/3 ≤ d := by
      have hs := h.part_size i
      change (1-ε)*n/2 ≤ d at hs
      nlinarith [mul_le_mul_of_nonneg_right hε1 hn]
    have hsq : (n/3)^2 ≤ d^2 := by gcongr
    have hsqm := mul_le_mul_of_nonneg_left hsq ha
    have hb := card_le_order_mul_degree B (δ*n) hB
    have hco := mul_le_mul_of_nonneg_right hδa (sq_nonneg n)
    change (B.card:ℝ) ≤ n*(δ*n) at hb
    change (B.card:ℝ) ≤ a*d^2
    nlinarith

#print axioms HostHyp.mono
#print axioms HostHyp.delete

end PartitionedTriangleAbsorption.BlowupB.F0Direct
