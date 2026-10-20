/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedTransportStage265

/-! # Transport avoiding previously used edges

Deleting a graph of maximum degree at most beta^2 n / 10^8 preserves enough
degree and nonextremality for signed transport. The certificate is built in
G minus F itself. Vertex deletion and simultaneous congestion are not asserted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.DeletedTransportStage266

open Finset BlowupB OnePart

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem degree_le_deleted_add (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj] (v : V) :
    G.degree v ≤ (G \ F).degree v + F.degree v := by
  classical
  have hs : G.neighborFinset v ⊆ (G \ F).neighborFinset v ∪ F.neighborFinset v := by
    intro w hw
    by_cases hf : F.Adj v w
    · exact mem_union_right _ (by simpa using hf)
    · exact mem_union_left _ (by simpa using And.intro (G.mem_neighborFinset v w |>.mp hw) hf)
  exact (card_le_card hs).trans (card_union_le _ _)

open scoped Classical in
/-- Extremality of a spanning subgraph transfers to its supergraph when the
lost degree fits inside the change in the extremality parameter. -/
theorem extremal_transfer (G H : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel H.Adj] (hHG : H ≤ G)
    (a b : ℝ) (hab : a ≤ b)
    (hd : ∀ v, (G.degree v : ℝ) ≤ H.degree v + (b - a) * Fintype.card V)
    (h : (1 - a) * Fintype.card V ≤
      ((univ.filter (fun w => (H.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - a) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((H.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)) :
    (1 - b) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + b) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - b) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ) := by
  classical
  have hn : (0 : ℝ) ≤ Fintype.card V := by positivity
  constructor
  · have hc := card_le_card (show
        univ.filter (fun w => (H.degree w : ℝ) ≤ (3 / 4 + a) * Fintype.card V) ⊆
        univ.filter (fun w => (G.degree w : ℝ) ≤ (3 / 4 + b) * Fintype.card V) from by
      intro w hw
      simp only [mem_filter, mem_univ, true_and] at hw ⊢
      linarith [hd w])
    have hc' : ((univ.filter (fun w => (H.degree w : ℝ) ≤
        (3 / 4 + a) * Fintype.card V)).card : ℝ) ≤
        (univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + b) * Fintype.card V)).card := by exact_mod_cast hc
    nlinarith [h.1, mul_nonneg (sub_nonneg.mpr hab) hn]
  · obtain ⟨T, hT⟩ := h.2
    refine ⟨T, ?_⟩
    have hc := card_le_card (filter_subset_filter
      (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)
      (SimpleGraph.edgeFinset_mono hHG))
    have hc' : ((H.edgeFinset.filter
        (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ) ≤
        (G.edgeFinset.filter
        (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card := by
      exact_mod_cast hc
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sq_nonneg (Fintype.card V : ℝ))]

open scoped Classical in
/-- Physical signed transport avoiding every edge of F. -/
theorem transport_avoiding_edges (G F : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableRel F.Adj]
    (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hn : 0 < Fintype.card V)
    (hdeg : ∀ w, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree w)
    (hF : ∀ w, (F.degree w : ℝ) ≤ b ^ 2 / 100000000 * Fintype.card V)
    (hnot : ¬ ((1 - b) * Fintype.card V ≤
      ((univ.filter (fun w => (G.degree w : ℝ) ≤
        (3 / 4 + b) * Fintype.card V)).card : ℝ) ∧
      ∃ T : Finset V, (1 - b) * (Fintype.card V : ℝ) ^ 2 / 4 ≤
        ((G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ)))
    {u v x y : V} (huv : (G \ F).Adj u v) (hxy : (G \ F).Adj x y) :
    PhysCostZ part1 triFam (G \ F)
      ((2 : ℤ) • (ind1 s(u, v) - ind1 s(x, y))) 116 := by
  classical
  have hbudget : b ^ 2 / 100000000 ≤ b - b / 4 := by nlinarith
  have hloss : ∀ w, (G.degree w : ℝ) ≤ (G \ F).degree w +
      b ^ 2 / 100000000 * Fintype.card V := by
    intro w
    have hd : (G.degree w : ℝ) ≤ (G \ F).degree w + F.degree w := by
      exact_mod_cast degree_le_deleted_add G F w
    linarith [hF w]
  apply SignedTransportStage265.nonextremal_transport_cost (G \ F)
    (b / 4) (b ^ 2 / 100000000) (by positivity) (by linarith) (by positivity)
    hn (by nlinarith [sq_nonneg b]) _ _ huv hxy
  · intro w
    linarith [hloss w, hdeg w]
  · intro hext
    apply hnot
    apply extremal_transfer G (G \ F) sdiff_le (b / 4) b (by linarith) _ hext
    intro w
    have hscale := mul_le_mul_of_nonneg_right hbudget
      (show (0 : ℝ) ≤ Fintype.card V by positivity)
    linarith [hloss w]

end PartitionedTriangleAbsorption.DeletedTransportStage266
