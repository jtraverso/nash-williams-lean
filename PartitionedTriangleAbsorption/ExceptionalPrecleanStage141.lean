/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupGeometryStage140

/-! # Making a small exceptional set independent

Every edge within the exceptional set is covered by a real triangle whose
third vertex is outside that set. The packing is constructed and has bounded
degree. This does not cover every edge incident with the exceptional set and
does not establish the matched cut quotas needed for the final application.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ExceptionalPrecleanStage141

open Finset AntiEdgeSelection MatchedQuotaStage140 RequestPackingStage140
open RootQuotaPackingStage124 OnePart

variable {V : Type*} [Fintype V] [DecidableEq V]

def within (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ x ∈ e, x ∈ S

theorem within_load (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (x : V) :
    incidentLoad (within G S) x ≤ S.card := by
  classical
  have hs : (within G S).filter (fun e => x ∈ e) ⊆ S.image (fun w => s(x, w)) := by
    intro e he
    obtain ⟨heB, hx⟩ := mem_filter.mp he
    have hS := (mem_filter.mp heB).2
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl
      · exact mem_image.mpr ⟨b, hS b (by simp), rfl⟩
      · exact mem_image.mpr ⟨a, hS a (by simp), Sym2.eq_swap⟩
  exact (card_le_card hs).trans (card_image_le)

theorem within_card (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    (within G S).card ≤ S.card * S.card := by
  classical
  have hs : within G S ⊆ (S ×ˢ S).image (fun w => s(w.1, w.2)) := by
    intro e he
    have hS := (mem_filter.mp he).2
    induction e using Sym2.ind with
    | _ a b =>
      exact mem_image.mpr ⟨(a, b), mem_product.mpr
        ⟨hS a (by simp), hS b (by simp)⟩, rfl⟩
  exact (card_le_card hs).trans ((card_image_le).trans_eq (card_product _ _))

theorem common_outside_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (u v : V) :
    G.degree u + G.degree v ≤ Fintype.card V +
      ((G.neighborFinset u ∩ G.neighborFinset v) \ S).card + S.card := by
  have hc := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have hu := card_le_card (subset_univ (G.neighborFinset u ∪ G.neighborFinset v))
  have hd := card_sdiff_add_card_inter (G.neighborFinset u ∩ G.neighborFinset v) S
  have hi := card_le_card (inter_subset_right :
    (G.neighborFinset u ∩ G.neighborFinset v) ∩ S ⊆ S)
  rw [SimpleGraph.card_neighborFinset_eq_degree,
    SimpleGraph.card_neighborFinset_eq_degree] at hc
  simp only [card_univ] at hu
  omega

/-- A small exceptional set can be made independent without any supplied
packing, matching, or common-neighbour hypothesis. -/
theorem exists_independent_preclean (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hsize : 40 * (S.card + 1) ≤ Fintype.card V) :
    ∃ Q : Finset (Sym2 V), Q ⊆ G.edgeFinset ∧ HasDecomp part1 triFam Q ∧
      DegBounded Q (4 * S.card + 2) ∧
      (∀ u ∈ S, ∀ v ∈ S, ¬ (G.deleteEdges (Q : Set (Sym2 V))).Adj u v) := by
  classical
  let B := within G S
  let u : B → V := edgeLeft B
  let v : B → V := edgeRight B
  let p : V → Fin 2 := fun x => if x ∈ S then 0 else 1
  let k : B → Fin 2 := fun _ => 1
  have hloop : ∀ e ∈ B, ¬ e.IsDiag :=
    fun e he => G.not_isDiag_of_mem_edgeFinset (mem_filter.mp he).1
  have huS : ∀ e : B, u e ∈ S := by
    intro e
    have hS := (mem_filter.mp e.property).2
    apply hS
    rw [← edge_rebuild B e]
    simp [u]
  have hvS : ∀ e : B, v e ∈ S := by
    intro e
    have hS := (mem_filter.mp e.property).2
    apply hS
    rw [← edge_rebuild B e]
    simp [v]
  have hbase : ∀ e : B, G.Adj (u e) (v e) := by
    intro e
    change s(u e, v e) ∈ G.edgeSet
    apply G.mem_edgeFinset.mp
    rw [show s(u e, v e) = e.val from edge_rebuild B e]
    exact (mem_filter.mp e.property).1
  have hp : ∀ e : B, p (u e) = p (v e) := by
    intro e
    simp [p, huS e, hvS e]
  have hk : ∀ e : B, k e ≠ p (u e) := by
    intro e
    simp [p, k, huS e]
  have hr : ∀ x, rootLoad univ u v x ≤ S.card := by
    intro x
    rw [rootLoad_edges B hloop]
    exact within_load G S x
  have hsupply : ∀ e : B, 8 * (S.card + 1) ≤ (candidates p G (u e) (v e) (k e)).card := by
    intro e
    have hc := common_outside_budget G S (u e) (v e)
    have heq : candidates p G (u e) (v e) (k e) =
        (G.neighborFinset (u e) ∩ G.neighborFinset (v e)) \ S := by
      ext w
      simp only [candidates, mem_filter, mem_univ, true_and, mem_sdiff, mem_inter,
        SimpleGraph.mem_neighborFinset, p, k]
      constructor
      · rintro ⟨ha, hb, hw⟩
        have hn : w ∉ S := by
          intro hwS
          simp [hwS] at hw
        exact ⟨⟨ha, hb.symm⟩, hn⟩
      · rintro ⟨⟨ha, hb⟩, hn⟩
        exact ⟨ha, hb.symm, by simp [hn]⟩
    rw [heq]
    have hcR : (G.degree (u e) : ℝ) + G.degree (v e) ≤ Fintype.card V +
        ((G.neighborFinset (u e) ∩ G.neighborFinset (v e)) \ S).card + S.card :=
      by exact_mod_cast hc
    have hnR : 40 * ((S.card : ℝ) + 1) ≤ Fintype.card V := by exact_mod_cast hsize
    have h : (8 * (S.card + 1) : ℕ) ≤
        ((G.neighborFinset (u e) ∩ G.neighborFinset (v e)) \ S).card := by
      have : (8 : ℝ) * (S.card + 1) ≤
          ((G.neighborFinset (u e) ∩ G.neighborFinset (v e)) \ S).card := by
        nlinarith [hdeg (u e), hdeg (v e)]
      exact_mod_cast this
    exact h
  have hb : 2 * (univ : Finset B).card +
      2 * (S.card + 2 * (S.card + 1)) * (S.card + 1) <
      (8 * (S.card + 1)) * (S.card + 1) := by
    have hc : (univ : Finset B).card ≤ S.card * S.card := by
      simpa only [card_univ, Fintype.card_coe] using within_card G S
    nlinarith
  obtain ⟨f, _, _, _, hQ, hdec, hcover, hbound⟩ :=
    exists_cleanup p G u v k univ S.card (S.card + 1) (8 * (S.card + 1))
      (fun e _ => hbase e) (fun e _ => hp e) (fun e _ => hk e)
      (oriented_injective B).injOn hr (fun e _ => hsupply e) hb
  refine ⟨packingEdges univ u v f, hQ, hdec, ?_, ?_⟩
  · convert hbound using 1
    push_cast
    ring
  · intro x hx y hy hxy
    have he : s(x, y) ∈ B := mem_filter.mpr ⟨G.mem_edgeFinset.mpr hxy.1, by
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption⟩
    let e : B := ⟨s(x, y), he⟩
    have h := hcover e (mem_univ e)
    rw [show s(u e, v e) = s(x, y) from edge_rebuild B e] at h
    exact hxy.2 ⟨h, hxy.1.ne⟩

/-- The constructed preclean preserves ordinary triangle divisibility. -/
theorem exists_divisible_independent_preclean (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hsize : 40 * (S.card + 1) ≤ Fintype.card V)
    (hdiv : IsIntDiv part1 triFam G.edgeFinset) :
    ∃ Q : Finset (Sym2 V), Q ⊆ G.edgeFinset ∧ HasDecomp part1 triFam Q ∧
      DegBounded Q (4 * S.card + 2) ∧
      IsIntDiv part1 triFam (G.deleteEdges (Q : Set (Sym2 V))).edgeFinset ∧
      (∀ u ∈ S, ∀ v ∈ S, ¬ (G.deleteEdges (Q : Set (Sym2 V))).Adj u v) := by
  obtain ⟨Q, hQ, hdec, hbound, hind⟩ := exists_independent_preclean G S hdeg hsize
  refine ⟨Q, hQ, hdec, hbound, ?_, hind⟩
  simpa only [SimpleGraph.edgeFinset_deleteEdges] using
    isIntDiv_sdiff_of_hasDecomp hdiv hdec hQ

end PartitionedTriangleAbsorption.ExceptionalPrecleanStage141
