/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.SignedCertificate
public import RequestProject.NW18.Defs

@[expose] public section

/-!
# Signed certificates on the actual 12.4 hosts and on their robust residues

* `signed_certificate_edgeSet`: the certificate for a divisible edge set `E ⊆ E(G)`
  (`Even3 E`: `3 ∣ |E|` and all degrees even, i.e. `IsIntDiv part1 triFam E`).
* `nonextHyp_of_host`: a 12.4 host (`3n ≤ 4δ(G)`, not `IsExtremal β G`, `0 < β ≤ 1`, `n > 0`)
  satisfies the Stage 265 hypotheses with `a = β`, `e = 0`.
* `nonextHyp_residual`: the residual graph `(G - F)[U]` of Stage 268 (with
  `n - |U| ≤ β² n / 10⁸` and `Δ(F) ≤ β² n / 10⁸`) satisfies them with `a = β/4`,
  `e = β² / (2·10⁷)`; this re-derives the residual degree and non-extremality exactly as in
  `VertexTransportStage268.transport_avoiding_vertices_edges`.
* `robust_signed_certificate`: hence every divisible edge set of `(G - F)[U]` has a physical
  signed certificate inside `(G - F)[U]` of cost `≤ 16741 |E|`.
-/

namespace NashWilliams18.ParityFill

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.BlowupB
  PartitionedTriangleAbsorption.OnePart

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem degw_indZ (E : Finset (Sym2 V)) (v : V) :
    degw (indZ E) v = AntiEdgeSelection.incidentLoad E v := by
  rw [degw, AntiEdgeSelection.incidentLoad, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  rw [← sum_subset (subset_univ E)]
  · refine sum_congr rfl fun e he => ?_
    simp [indZ, he]
  · intro e _ he
    simp [indZ, he]

theorem l1_indZ (E : Finset (Sym2 V)) : l1 (indZ E) = E.card := by
  rw [l1, ← sum_indZ]
  refine sum_congr rfl fun e _ => ?_
  simp only [indZ]; split_ifs <;> simp

/-- **Certificate for a divisible piece.**  Under the Stage 265 hypotheses, every edge set
`E ⊆ E(G)` with `3 ∣ |E|` and all degrees even has a physical signed triangle certificate in
`G` of cost `≤ 16741 |E|`. -/
theorem signed_certificate_edgeSet {G : SimpleGraph V} [DecidableRel G.Adj] {a e : ℝ}
    (H : NonextHyp G a e) (E : Finset (Sym2 V)) (hE : ∀ f ∈ E, f ∈ G.edgeSet)
    (hdiv : Even3 E) :
    PhysCostZ part1 triFam G (indZ E) (16741 * E.card) := by
  have := signed_certificate H (indZ E) (fun f hf => hE f (by
      by_contra h; exact hf (by simp [indZ, h])))
    (fun v => by
      rw [degw_indZ]
      obtain ⟨k, hk⟩ := hdiv.2 v
      exact ⟨k, by rw [hk]; push_cast; ring⟩)
    (by rw [sum_indZ]; exact_mod_cast hdiv.1)
  rwa [l1_indZ] at this

/-- A 12.4 host satisfies the Stage 265 hypotheses with `a = β`, `e = 0`. -/
theorem nonextHyp_of_host (G : SimpleGraph V) [DecidableRel G.Adj] {β : ℝ}
    (hβ : 0 < β) (hβ1 : β ≤ 1) (hn : 0 < Fintype.card V)
    (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) (hnx : ¬ IsExtremal β G) :
    NonextHyp G β 0 := by
  refine ⟨hβ, hβ1, le_rfl, hn, by nlinarith, fun v => ?_, fun hext => hnx ?_⟩
  · have h1 : (3 : ℝ) * Fintype.card V ≤ 4 * G.minDegree := by exact_mod_cast hδ
    have h2 : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast G.minDegree_le_degree v
    linarith
  · obtain ⟨h1, T, hT⟩ := hext
    refine ⟨by convert h1 using 3, T, ?_⟩
    unfold NashWilliams18.cutSize
    convert hT using 3

open scoped Classical in
/-- **Residual hypotheses** (Stage 268 parameters): if `δ(G) ≥ 3n/4`, `G` is not `b`-extremal,
`n - |U| ≤ b² n / 10⁸` and `Δ(F) ≤ b² n / 10⁸`, then `(G - F)[U]` satisfies the Stage 265
hypotheses with `a = b/4` and `e = b² / (2·10⁷)`. -/
theorem nonextHyp_residual (G F : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel F.Adj]
    (U : Finset V) (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) (hn : 0 < Fintype.card V)
    (hU : (Fintype.card V : ℝ) - U.card ≤ b ^ 2 / 100000000 * Fintype.card V)
    (hdeg : ∀ w, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree w)
    (hF : ∀ w, (F.degree w : ℝ) ≤ b ^ 2 / 100000000 * Fintype.card V)
    (hnot : ¬ ExtrF G b) :
    NonextHyp ((G \ F).induce (↑U : Set V)) (b / 4) (b ^ 2 / 20000000) := by
  classical
  let n : ℝ := Fintype.card V
  let N : ℝ := U.card
  let z := (n - N) / n
  let d := b ^ 2 / 100000000
  let H := (G \ F).induce (↑U : Set V)
  have hnpos : 0 < n := by dsimp [n]; exact_mod_cast hn
  have hNle : N ≤ n := by dsimp [N, n]; exact_mod_cast card_le_univ (s := U)
  have hzrel : z * n = n - N := div_mul_cancel₀ _ hnpos.ne'
  have hNrel : (1 - z) * n = N := by nlinarith [hzrel]
  have hz : 0 ≤ z := div_nonneg (sub_nonneg.mpr hNle) hnpos.le
  have hzs : 100000000 * z ≤ b ^ 2 := by
    apply (mul_le_mul_iff_left₀ hnpos).mp
    dsimp [n, N] at hzrel ⊢
    nlinarith [hU]
  obtain ⟨hpos, he, hcount, hhigh, hcut⟩ :=
    VertexTransportStage268.deletion_margins b z d hb hb1 hz hzs (by dsimp [d]; linarith)
  have hcard : (Fintype.card (↑U : Set V) : ℝ) = N := by simp [N]
  have hNpos : 0 < N := by rw [← hNrel]; positivity
  have hlos (w : (↑U : Set V)) :
      (G.degree w.val : ℝ) ≤ H.degree w + (z + d) * n := by
    have h1 : (G.degree w.val : ℝ) ≤ (G \ F).degree w.val + F.degree w.val := by
      exact_mod_cast DeletedTransportStage266.degree_le_deleted_add G F w.val
    have h2 : ((G \ F).degree w.val : ℝ) + N ≤ H.degree w + n := by
      dsimp [N, H, n]
      exact_mod_cast VertexTransportStage268.degree_induce_loss (G \ F) U w
    have hf : (F.degree w.val : ℝ) ≤ d * n := hF w.val
    nlinarith [hzrel]
  refine ⟨by positivity, by linarith, by positivity, ?_, by nlinarith [sq_nonneg b], ?_, ?_⟩
  · have : (0 : ℝ) < Fintype.card (↑U : Set V) := by rwa [hcard]
    exact_mod_cast this
  · intro w
    rw [hcard]
    have hscaled := mul_le_mul_of_nonneg_right he hnpos.le
    rw [mul_assoc, hNrel] at hscaled
    have hw : (3 / 4 : ℝ) * n ≤ G.degree w.val := hdeg w.val
    nlinarith [hlos w, hzrel]
  · intro hext
    apply hnot
    have hscaleCount := mul_le_mul_of_nonneg_right hcount hnpos.le
    rw [mul_assoc, hNrel] at hscaleCount
    have hscaleHigh := mul_le_mul_of_nonneg_right hhigh hnpos.le
    have hscaleCut := mul_le_mul_of_nonneg_right hcut (sq_nonneg n)
    have hcutN : (1 - b) * n ^ 2 ≤ (1 - b / 4) * N ^ 2 := by
      rw [← hNrel]
      nlinarith [hscaleCut]
    constructor
    · let L := univ.filter (fun w : (↑U : Set V) =>
        (H.degree w : ℝ) ≤ (3 / 4 + b / 4) * Fintype.card (↑U : Set V))
      have hsub : L.image Subtype.val ⊆ univ.filter (fun w =>
          (G.degree w : ℝ) ≤ (3 / 4 + b) * Fintype.card V) := by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := mem_image.mp hw
        have hv' : (H.degree v : ℝ) ≤ (3 / 4 + b / 4) * N := by
          simpa only [L, mem_filter, mem_univ, true_and, hcard] using hv
        simp only [mem_filter, mem_univ, true_and]
        change (G.degree v.val : ℝ) ≤ (3 / 4 + b) * n
        nlinarith [hlos v, hNrel]
      have hc := card_le_card hsub
      rw [card_image_iff.mpr (fun _ _ _ _ h => Subtype.val_injective h)] at hc
      have hc' : (L.card : ℝ) ≤ (univ.filter (fun w =>
          (G.degree w : ℝ) ≤ (3 / 4 + b) * Fintype.card V)).card := by exact_mod_cast hc
      have hel : (1 - b / 4) * N ≤ (L.card : ℝ) := by simpa only [L, hcard] using hext.1
      exact hscaleCount.trans (hel.trans hc')
    · obtain ⟨T, hT⟩ := hext.2
      refine ⟨T.image Subtype.val, ?_⟩
      have hc := VertexTransportStage268.cut_induce_le (G \ F) U T
      have hc2 : ((@SimpleGraph.edgeFinset V (G \ F) (G \ F).fintypeEdgeSet).filter
          (fun edge => ∃ x y, edge = s(x, y) ∧
            x ∈ T.image Subtype.val ∧ y ∉ T.image Subtype.val)).card ≤
          (G.edgeFinset.filter
          (fun edge => ∃ x y, edge = s(x, y) ∧
            x ∈ T.image Subtype.val ∧ y ∉ T.image Subtype.val)).card := by
        apply card_le_card
        intro edge hedge
        obtain ⟨he, x, y, rfl, hx, hy⟩ := mem_filter.mp hedge
        refine mem_filter.mpr ⟨?_, x, y, rfl, hx, hy⟩
        simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he ⊢
        exact he.1
      have hc' : ((H.edgeFinset.filter (fun edge => ∃ x y,
          edge = s(x, y) ∧ x ∈ T ∧ y ∉ T)).card : ℝ) ≤
          (G.edgeFinset.filter (fun edge => ∃ x y,
          edge = s(x, y) ∧ x ∈ T.image Subtype.val ∧ y ∉ T.image Subtype.val)).card := by
        exact_mod_cast hc.trans hc2
      rw [hcard] at hT
      change (1 - b) * n ^ 2 / 4 ≤ _
      linarith

open scoped Classical in
/-- **Robust signed certificate for divisible pieces.**  If `δ(G) ≥ 3n/4`, `G` is not
`b`-extremal (`0 < b ≤ 1`), at most `b² n/10⁸` vertices are deleted (`U` is kept) and the removed
graph `F` has maximum degree `≤ b² n/10⁸`, then every edge set `E` of `(G - F)[U]` with
`3 ∣ |E|` and all degrees even has a physical signed triangle certificate **inside**
`(G - F)[U]`, of cost `≤ 16741 |E|`. -/
theorem robust_signed_certificate (G F : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel F.Adj] (U : Finset V) (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hn : 0 < Fintype.card V)
    (hU : (Fintype.card V : ℝ) - U.card ≤ b ^ 2 / 100000000 * Fintype.card V)
    (hdeg : ∀ w, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree w)
    (hF : ∀ w, (F.degree w : ℝ) ≤ b ^ 2 / 100000000 * Fintype.card V)
    (hnot : ¬ ExtrF G b)
    (E : Finset (Sym2 (↑U : Set V)))
    (hE : ∀ f ∈ E, f ∈ ((G \ F).induce (↑U : Set V)).edgeSet) (hdiv : Even3 E) :
    PhysCostZ part1 triFam ((G \ F).induce (↑U : Set V)) (indZ E) (16741 * E.card) :=
  signed_certificate_edgeSet (nonextHyp_residual G F U b hb hb1 hn hU hdeg hF hnot) E hE hdiv

end NashWilliams18.ParityFill
