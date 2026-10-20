/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.DeletedTransportStage266

/-! # Transport after deleting vertices and edges

The retained vertex subtype is explicit. No degree bound on the edges
incident with deleted vertices is assumed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.VertexTransportStage268

open Finset BlowupB OnePart

theorem deletion_margins (b z d : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hz : 0 ≤ z)
    (hzsmall : 100000000 * z ≤ b ^ 2) (hdsmall : 100000000 * d ≤ b ^ 2) :
    0 < 1 - z ∧
    b ^ 2 / 20000000 * (1 - z) ≥ z / 4 + d ∧
    (1 - b / 4) * (1 - z) ≥ 1 - b ∧
    (3 / 4 + b / 4) * (1 - z) + z + d ≤ 3 / 4 + b ∧
    (1 - b / 4) * (1 - z) ^ 2 ≥ 1 - b := by
  have hb2 : b ^ 2 ≤ b := by nlinarith
  have hz1 : z ≤ 1 / 2 := by nlinarith
  have hzb : 100000000 * z ≤ b := hzsmall.trans hb2
  have hdb : 100000000 * d ≤ b := hdsmall.trans hb2
  have hbz := mul_nonneg hb.le hz
  have he := mul_nonneg (sq_nonneg b) (show 0 ≤ 1 / 2 - z by linarith)
  have hsq := mul_nonneg (show 0 ≤ 1 - b / 4 by linarith) (sq_nonneg z)
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩ <;> nlinarith

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
open scoped Classical in
theorem degree_induce_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (v : (↑U : Set V)) :
    G.degree v.val + U.card ≤ (G.induce (↑U : Set V)).degree v + Fintype.card V := by
  classical
  have hc := card_union_add_card_inter U (G.neighborFinset v.val)
  have hu := card_le_univ (s := U ∪ G.neighborFinset v.val)
  have heq : U ∩ G.neighborFinset v.val = U.filter (G.Adj v.val) := by
    ext w
    simp
  rw [heq, ← GoodRemaindersStage261.induced_degree_eq_filter G U v,
    SimpleGraph.card_neighborFinset_eq_degree] at hc
  omega

open scoped Classical in
theorem cut_induce_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (T : Finset (↑U : Set V)) :
    ((G.induce (↑U : Set V)).edgeFinset.filter
      (fun e => ∃ x y, e = s(x,y) ∧ x ∈ T ∧ y ∉ T)).card ≤
    (G.edgeFinset.filter
      (fun e => ∃ x y, e = s(x,y) ∧ x ∈ T.image Subtype.val ∧
        y ∉ T.image Subtype.val)).card := by
  classical
  apply card_le_card_of_injOn (fun e => e.map Subtype.val)
  · intro e he
    obtain ⟨heG, x, y, rfl, hx, hy⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨?_, x.val, y.val, rfl, mem_image.mpr ⟨x,hx,rfl⟩, ?_⟩
    · simpa using heG
    · intro hy'
      obtain ⟨w, hw, hwv⟩ := mem_image.mp hy'
      exact hy (Subtype.val_injective hwv ▸ hw)
  · intro e he f hf hef
    exact (Sym2.map.injective Subtype.val_injective) hef

set_option maxHeartbeats 800000 in
-- Nonlinear rescaling of the induced graph and both extremality witnesses.
open scoped Classical in
/-- Simultaneous exclusion: the certificate lives on the retained vertices
and uses only edges outside the forbidden graph. -/
theorem transport_avoiding_vertices_edges (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (U : Finset V)
    (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hn : 0 < Fintype.card V)
    (hU : (Fintype.card V : ℝ) - U.card ≤ b ^ 2 / 100000000 * Fintype.card V)
    (hdeg : ∀ w, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree w)
    (hF : ∀ w, (F.degree w : ℝ) ≤ b ^ 2 / 100000000 * Fintype.card V)
    (hnot : ¬ ((1 - b) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + b) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - b) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)))
    {u v x y : (↑U : Set V)}
    (huv : ((G \ F).induce (↑U : Set V)).Adj u v)
    (hxy : ((G \ F).induce (↑U : Set V)).Adj x y) :
    PhysCostZ part1 triFam ((G \ F).induce (↑U : Set V))
      ((2 : ℤ) • (ind1 s(u,v) - ind1 s(x,y))) 116 := by
  classical
  let n : ℝ := Fintype.card V
  let N : ℝ := U.card
  let z := (n-N)/n
  let d := b^2/100000000
  let H := (G \ F).induce (↑U : Set V)
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hNle : N ≤ n := by dsimp [N,n]; exact_mod_cast card_le_univ (s := U)
  have hzrel : z*n = n-N := div_mul_cancel₀ _ hnpos.ne'
  have hNrel : (1-z)*n = N := by nlinarith [hzrel]
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hNle) hnpos.le
  have hzs : 100000000*z ≤ b^2 := by
    apply (mul_le_mul_iff_left₀ hnpos).mp
    dsimp [n,N] at hzrel ⊢
    nlinarith [hU]
  obtain ⟨hpos, he, hcount, hhigh, hcut⟩ :=
    deletion_margins b z d hb hb1 hz hzs (by dsimp [d]; linarith)
  have hcard : (Fintype.card (↑U : Set V) : ℝ) = N := by simp [N]
  have hNpos : 0 < N := by rw [← hNrel]; positivity
  have hlos (w : (↑U : Set V)) :
      (G.degree w.val : ℝ) ≤ H.degree w + (z+d)*n := by
    have h1 : (G.degree w.val : ℝ) ≤ (G \ F).degree w.val + F.degree w.val := by
      exact_mod_cast DeletedTransportStage266.degree_le_deleted_add G F w.val
    have h2 : ((G \ F).degree w.val : ℝ) + N ≤ H.degree w + n := by
      dsimp [N,H,n]
      exact_mod_cast degree_induce_loss (G \ F) U w
    have hf : (F.degree w.val : ℝ) ≤ d*n := hF w.val
    nlinarith [hzrel]
  apply SignedTransportStage265.nonextremal_transport_cost H (b/4) (b^2/20000000)
    (by positivity) (by linarith) (by positivity) _ (by nlinarith [sq_nonneg b]) _ _ huv hxy
  · have : (0 : ℝ) < Fintype.card (↑U : Set V) := by rwa [hcard]
    exact_mod_cast this
  · intro w
    rw [hcard]
    have hscaled := mul_le_mul_of_nonneg_right he hnpos.le
    rw [mul_assoc, hNrel] at hscaled
    have hw : (3/4:ℝ)*n ≤ G.degree w.val := hdeg w.val
    nlinarith [hlos w, hzrel]
  · intro hext
    apply hnot
    have hscaleCount := mul_le_mul_of_nonneg_right hcount hnpos.le
    rw [mul_assoc, hNrel] at hscaleCount
    have hscaleHigh := mul_le_mul_of_nonneg_right hhigh hnpos.le
    have hscaleCut := mul_le_mul_of_nonneg_right hcut (sq_nonneg n)
    have hcutN : (1-b)*n^2 ≤ (1-b/4)*N^2 := by
      rw [← hNrel]
      nlinarith [hscaleCut]
    constructor
    · let L := univ.filter (fun w : (↑U : Set V) =>
        (H.degree w : ℝ) ≤ (3/4+b/4)*Fintype.card (↑U : Set V))
      have hsub : L.image Subtype.val ⊆ univ.filter (fun w =>
          (G.degree w : ℝ) ≤ (3/4+b)*Fintype.card V) := by
        intro w hw
        obtain ⟨v,hv,rfl⟩ := mem_image.mp hw
        have hv' : (H.degree v : ℝ) ≤ (3/4+b/4)*N := by
          simpa only [L, mem_filter, mem_univ, true_and, hcard] using hv
        simp only [mem_filter, mem_univ, true_and]
        change (G.degree v.val : ℝ) ≤ (3/4+b)*n
        nlinarith [hlos v, hNrel]
      have hc := card_le_card hsub
      rw [card_image_iff.mpr (fun _ _ _ _ h => Subtype.val_injective h)] at hc
      have hc' : (L.card : ℝ) ≤ (univ.filter (fun w =>
          (G.degree w : ℝ) ≤ (3/4+b)*Fintype.card V)).card := by exact_mod_cast hc
      have hel : (1-b/4)*N ≤ (L.card : ℝ) := by simpa only [L,hcard] using hext.1
      exact hscaleCount.trans (hel.trans hc')
    · obtain ⟨T,hT⟩ := hext.2
      refine ⟨T.image Subtype.val, ?_⟩
      have hc := cut_induce_le (G \ F) U T
      have hc2 : ((@SimpleGraph.edgeFinset V (G \ F) (G \ F).fintypeEdgeSet).filter
          (fun edge => ∃ x y, edge = s(x,y) ∧
            x ∈ T.image Subtype.val ∧ y ∉ T.image Subtype.val)).card ≤
          (G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x,y) ∧
            x ∈ T.image Subtype.val ∧ y ∉ T.image Subtype.val)).card := by
        apply card_le_card
        intro edge hedge
        obtain ⟨he, x, y, rfl, hx, hy⟩ := mem_filter.mp hedge
        refine mem_filter.mpr ⟨?_, x, y, rfl, hx, hy⟩
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        exact he.1
      have hc' : ((H.edgeFinset.filter (fun edge => ∃ x y,
          edge = s(x,y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ) ≤
          (G.edgeFinset.filter (fun edge => ∃ x y,
          edge = s(x,y) ∧ x ∈ T.image Subtype.val ∧ y ∉ T.image Subtype.val)).card := by
        exact_mod_cast hc.trans hc2
      rw [hcard] at hT
      change (1-b)*n^2/4 ≤ _
      linarith

end PartitionedTriangleAbsorption.VertexTransportStage268
