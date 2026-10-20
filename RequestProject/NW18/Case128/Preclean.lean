/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128.GlobalQuota
public import PartitionedTriangleAbsorption.ExceptionalPrecleanStage141

@[expose] public section

/-!
# Case (5): a typed pre-clean of the edges inside the exceptional set

Every edge `ac` with both ends in the exceptional set `S` is covered by a triangle `acw` with
`w ∉ S` in a prescribed class `tgt(ac)`; the triangles are edge-disjoint and of bounded degree.
This is Claim 12.8.9 (for the edges `O₁`, with a third class) together with the part of
Claim 12.8.10 that treats the edges `O₂` (with a matched class of an allowed colour).  The
construction is the greedy packing `RequestPackingStage140.exists_cleanup`, applied with the
labelling that puts `S` into a fifth class.
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 AntiEdgeSelection
open RequestPackingStage140 RootQuotaPackingStage124 ExceptionalPrecleanStage141

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Typed pre-clean.**  If every edge `ac` inside `S` has at least `8(|S|+1)` common
neighbours outside `S` in the class `tgt(ac)`, then the edges inside `S` are covered by
edge-disjoint triangles `acw` of `G` with `w ∉ S` in class `tgt(ac)`, every vertex lies on at
most `4|S|+2` of their edges, and every vertex of `S` lies in at most `|S|` of them. -/
theorem exists_typed_preclean (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (tgt : Sym2 V → Fin 4)
    (hsupply : ∀ a ∈ S, ∀ c ∈ S, G.Adj a c →
      8 * (S.card + 1) ≤
        (univ.filter fun w => w ∉ S ∧ p w = tgt s(a, c) ∧ G.Adj a w ∧ G.Adj c w).card) :
    ∃ D : Finset (Finset V),
      (∀ t ∈ D, G.IsNClique 3 t) ∧ (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ t ∈ D, ∃ a c w, t = {a, c, w} ∧ a ∈ S ∧ c ∈ S ∧ w ∉ S ∧ p w = tgt s(a, c)) ∧
      (∀ a ∈ S, ∀ c ∈ S, G.Adj a c → s(a, c) ∈ D.biUnion triEdges) ∧
      DegBounded (D.biUnion triEdges) (4 * S.card + 2) ∧
      (∀ x ∈ S, (D.filter fun t => x ∈ t).card ≤ S.card) := by
  classical
  let B := within G S
  let u : B → V := edgeLeft B
  let v : B → V := edgeRight B
  let p' : V → Fin 5 := fun x => if x ∈ S then 4 else (p x).castSucc
  let k : B → Fin 5 := fun e => (tgt e.val).castSucc
  have hloop : ∀ e ∈ B, ¬ e.IsDiag :=
    fun e he => G.not_isDiag_of_mem_edgeFinset (mem_filter.mp he).1
  have hrebuild : ∀ e : B, s(u e, v e) = e.val := fun e => edge_rebuild B e
  have huS : ∀ e : B, u e ∈ S := by
    intro e
    have hS := (mem_filter.mp e.property).2
    apply hS
    rw [← hrebuild e]
    simp
  have hvS : ∀ e : B, v e ∈ S := by
    intro e
    have hS := (mem_filter.mp e.property).2
    apply hS
    rw [← hrebuild e]
    simp
  have hbase : ∀ e : B, G.Adj (u e) (v e) := by
    intro e
    change s(u e, v e) ∈ G.edgeSet
    apply G.mem_edgeFinset.mp
    rw [hrebuild e]
    exact (mem_filter.mp e.property).1
  have hp : ∀ e : B, p' (u e) = p' (v e) := by
    intro e
    simp [p', huS e, hvS e]
  have hk : ∀ e : B, k e ≠ p' (u e) := by
    intro e
    simp only [p', k, huS e, if_true]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  have hr : ∀ x, rootLoad univ u v x ≤ S.card := by
    intro x
    rw [rootLoad_edges B hloop]
    exact within_load G S x
  have hcand : ∀ e : B, candidates p' G (u e) (v e) (k e) =
      univ.filter fun w => w ∉ S ∧ p w = tgt s(u e, v e) ∧ G.Adj (u e) w ∧ G.Adj (v e) w := by
    intro e
    ext w
    simp only [candidates, mem_filter, mem_univ, true_and, p', k, hrebuild e]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hw : w ∈ S
      · simp only [hw, if_true] at h3
        have := congrArg Fin.val h3
        simp at this
        omega
      · simp only [hw, if_false] at h3
        exact ⟨hw, Fin.castSucc_injective _ h3, h1, h2.symm⟩
    · rintro ⟨hw, hpw, h1, h2⟩
      exact ⟨h1, h2.symm, by simp [hw, hpw]⟩
  have hsup : ∀ e : B, 8 * (S.card + 1) ≤ (candidates p' G (u e) (v e) (k e)).card := by
    intro e
    rw [hcand e]
    exact hsupply (u e) (huS e) (v e) (hvS e) (hbase e)
  have hb : 2 * (univ : Finset B).card +
      2 * (S.card + 2 * (S.card + 1)) * (S.card + 1) <
      (8 * (S.card + 1)) * (S.card + 1) := by
    have hc : (univ : Finset B).card ≤ S.card * S.card := by
      simpa only [card_univ, Fintype.card_coe] using within_card G S
    nlinarith
  obtain ⟨f, hf, hdis, -, -, -, -, hbound⟩ :=
    exists_cleanup p' G u v k univ S.card (S.card + 1) (8 * (S.card + 1))
      (fun e _ => hbase e) (fun e _ => hp e) (fun e _ => hk e)
      (oriented_injective B).injOn hr (fun e _ => hsup e) hb
  -- properties of the third vertices
  have hfS : ∀ e : B, f e ∉ S ∧ p (f e) = tgt s(u e, v e) := by
    intro e
    have h := (hf e (mem_univ e)).2.2
    simp only [p', k] at h
    by_cases hw : f e ∈ S
    · simp only [hw, if_true] at h
      have := congrArg Fin.val h
      simp at this
      omega
    · simp only [hw, if_false] at h
      exact ⟨hw, by rw [hrebuild e]; exact Fin.castSucc_injective _ h⟩
  have hne : ∀ e : B, u e ≠ v e ∧ u e ≠ f e ∧ v e ≠ f e := by
    intro e
    refine ⟨(hbase e).ne, ?_, ?_⟩
    · exact fun h => (hfS e).1 (h ▸ huS e)
    · exact fun h => (hfS e).1 (h ▸ hvS e)
  let tri : B → Finset V := fun e => {u e, v e, f e}
  have htriE : ∀ e : B, triEdges (tri e) = TypedCorrectionFamily.edges (u e) (v e) (f e) := by
    intro e
    obtain ⟨h1, h2, h3⟩ := hne e
    rw [triEdges_three h1 h2 h3]
    rfl
  let D := (univ : Finset B).image tri
  have hD : ∀ t, t ∈ D ↔ ∃ e : B, tri e = t := by
    intro t
    simp [D]
  have hunion : D.biUnion triEdges = packingEdges univ u v f := by
    ext x
    simp only [mem_biUnion, packingEdges, hD]
    constructor
    · rintro ⟨t, ⟨e, rfl⟩, hx⟩
      exact ⟨e, mem_univ _, by rwa [htriE e] at hx⟩
    · rintro ⟨e, -, hx⟩
      exact ⟨tri e, ⟨e, rfl⟩, by rwa [htriE e]⟩
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨e, rfl⟩ := (hD t).mp ht
    exact SimpleGraph.is3Clique_triple_iff.mpr ⟨hbase e, (hf e (mem_univ e)).1,
      (hf e (mem_univ e)).2.1.symm⟩
  · intro t ht t' ht' htt'
    obtain ⟨e, rfl⟩ := (hD t).mp ht
    obtain ⟨e', rfl⟩ := (hD t').mp ht'
    have hee' : e ≠ e' := fun h => htt' (h ▸ rfl)
    change Disjoint (triEdges (tri e)) (triEdges (tri e'))
    rw [htriE e, htriE e']
    exact hdis (mem_coe.mpr (mem_univ e)) (mem_coe.mpr (mem_univ e')) hee'
  · intro t ht
    obtain ⟨e, rfl⟩ := (hD t).mp ht
    exact ⟨u e, v e, f e, rfl, huS e, hvS e, (hfS e).1, (hfS e).2⟩
  · intro a ha c hc hac
    have he : s(a, c) ∈ B := mem_filter.mpr ⟨G.mem_edgeFinset.mpr hac, by
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption⟩
    let e : B := ⟨s(a, c), he⟩
    refine mem_biUnion.mpr ⟨tri e, (hD _).mpr ⟨e, rfl⟩, ?_⟩
    rw [htriE e, show s(a, c) = s(u e, v e) from (hrebuild e).symm]
    simp [TypedCorrectionFamily.edges]
  · rw [hunion]
    convert hbound using 1
    push_cast
    ring
  · intro x hx
    have hsub : D.filter (fun t => x ∈ t) ⊆
        ((univ : Finset B).filter fun e => x ∈ e.val).image tri := by
      intro t ht
      obtain ⟨htD, hxt⟩ := mem_filter.mp ht
      obtain ⟨e, rfl⟩ := (hD t).mp htD
      refine mem_image.mpr ⟨e, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      rw [← hrebuild e]
      simp only [tri, mem_insert, mem_singleton] at hxt
      rcases hxt with rfl | rfl | rfl
      · simp
      · simp
      · exact absurd hx (hfS e).1
    refine (card_le_card hsub).trans (card_image_le.trans ?_)
    have hload := within_load G S x
    unfold incidentLoad at hload
    refine le_trans ?_ hload
    have : ((univ : Finset B).filter fun e => x ∈ e.val).card =
        (B.attach.filter fun e => x ∈ e.val).card := rfl
    rw [this, ← card_map (Function.Embedding.subtype _)]
    apply card_le_card
    intro y hy
    obtain ⟨e, he, rfl⟩ := mem_map.mp hy
    exact mem_filter.mpr ⟨e.property, (mem_filter.mp he).2⟩

end NashWilliams18.C128
