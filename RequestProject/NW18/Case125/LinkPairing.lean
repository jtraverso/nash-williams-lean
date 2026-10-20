/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Pairing

@[expose] public section

/-!
# Perfect pairings of a link with few pairs inside one side

The combinatorial heart of the One Oddball Cleaning Lemma 15.7: the (available) link of a
vertex `z` is split into the part `P` on the side of `z` and the part `Q` on the other side,
plus a small set `S` of exceptional vertices.  If every non-exceptional vertex is adjacent to
almost all of the other side and to "enough" of its own side, and every exceptional vertex has
many neighbours in `Q`, then `P ∪ Q` has a perfect pairing with at most
`(|P| + 2|S| − |Q|) / 2` pairs inside `P`.  This replaces Pósa's theorem used in the paper:
we pair inside the larger side by `exists_pairing_large` and then complete by a dense
bipartite matching (`PartitionedTriangleAbsorption.PhysicalStarMatching.exists_matching_between_sets`).
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [DecidableEq V]

lemma linkPairing_card_sdiff {s t : Finset V} (h : s ⊆ t) : (t \ s).card = t.card - s.card := by
  have := card_sdiff_add_card_inter t s
  rw [inter_eq_right.mpr h] at this
  omega

/-- **Core pairing.**  `X`, `Y` disjoint, `|X| ≤ |Y|`, `|X| + |Y|` even; every vertex has at most
`e` non-neighbours on the other side, every vertex of `Y` at most `c` non-neighbours in `Y`.
Then `X ∪ Y` has a perfect pairing all of whose pairs end in `Y`, exactly `(|Y| − |X|)/2` of
them starting in `Y`. -/
lemma link_pairing_core (H : SimpleGraph V) [DecidableRel H.Adj] (X Y : Finset V) (e c : ℕ)
    (hXY : Disjoint X Y) (hle : X.card ≤ Y.card) (heven : Even (X.card + Y.card))
    (hXe : ∀ x ∈ X, (Y.filter fun y => ¬ H.Adj x y).card ≤ e)
    (hYe : ∀ y ∈ Y, (X.filter fun x => ¬ H.Adj y x).card ≤ e)
    (hYc : ∀ y ∈ Y, (Y.filter fun w => ¬ H.Adj y w).card ≤ c)
    (hX : 2 * e + 1 ≤ X.card) (hc : 2 * c ≤ X.card + Y.card) :
    ∃ M : Finset (V × V), IsPairing H M ∧ verts M = X ∪ Y ∧ (∀ q ∈ M, q.2 ∈ Y) ∧
      2 * (M.filter fun q => q.1 ∈ Y).card + X.card = Y.card := by
  obtain ⟨k, hk⟩ := heven
  set t := (Y.card - X.card) / 2 with ht
  have h2t : 2 * t = Y.card - X.card := by omega
  obtain ⟨M2, hM2, hM2Y, hM2c⟩ := exists_pairing_large H Y (Y.card - c) t
    (fun y hy => by
      have h1 := card_filter_add_card_filter_not (s := Y) (p := H.Adj y)
      have h2 := hYc y hy
      omega) (by omega) (by omega)
  set Y'' := Y \ verts M2 with hY''
  have hY''c : Y''.card = X.card := by
    rw [hY'', linkPairing_card_sdiff hM2Y, hM2.card_verts, hM2c]; omega
  have hY''Y : Y'' ⊆ Y := sdiff_subset
  have hXY'' : Disjoint X Y'' := hXY.mono_right hY''Y
  obtain ⟨f, hf⟩ := PartitionedTriangleAbsorption.PhysicalStarMatching.exists_matching_between_sets H X Y'' e hY''c.symm
    (by omega)
    (fun x hx => (card_le_card (filter_subset_filter _ hY''Y)).trans (hXe x hx))
    (fun y hy => by
      have := hYe y (hY''Y hy)
      simpa only [H.adj_comm] using this)
  obtain ⟨M3, hM3, hM3v, hM3o⟩ := pairing_of_equiv H X Y'' hXY'' f hf
  have hdisj : Disjoint (verts M2) (verts M3) := by
    rw [hM3v]
    refine disjoint_union_right.mpr ⟨(hXY.mono_right hM2Y).symm, ?_⟩
    exact disjoint_sdiff
  refine ⟨M2 ∪ M3, hM2.union hM3 hdisj, ?_, ?_, ?_⟩
  · rw [verts_union, hM3v]
    ext w
    simp only [mem_union, hY'', mem_sdiff]
    constructor
    · rintro (h | h | h)
      · exact Or.inr (hM2Y h)
      · exact Or.inl h
      · exact Or.inr h.1
    · rintro (h | h)
      · exact Or.inr (Or.inl h)
      · by_cases hw : w ∈ verts M2
        · exact Or.inl hw
        · exact Or.inr (Or.inr ⟨h, hw⟩)
  · intro q hq
    rcases mem_union.mp hq with h | h
    · exact hM2Y (mem_verts.mpr ⟨q, h, Or.inr rfl⟩)
    · exact hY''Y (hM3o q h).2
  · have : (M2 ∪ M3).filter (fun q => q.1 ∈ Y) = M2 := by
      rw [filter_union, filter_true_of_mem, filter_false_of_mem, union_empty]
      · intro q hq hqY
        exact disjoint_left.mp hXY (hM3o q hq).1 hqY
      · intro q hq
        exact hM2Y (mem_verts.mpr ⟨q, hq, Or.inl rfl⟩)
    rw [this, hM2c]; omega

/-- **Link pairing.**  `P`, `Q` disjoint with `|P| + |Q|` even and `S ⊆ P ∪ Q` exceptional.
Every vertex of `S` has at least `|S|` neighbours in `Q ∖ S`; every vertex outside `S` has at
most `e` non-neighbours on the other side and at most `c` in its own side.  Under the size
conditions below, `P ∪ Q` has a perfect pairing with at most `(|P| + 2|S| − |Q|)/2` pairs inside
`P` (in particular none when `|P| + 2|S| ≤ |Q|`). -/
lemma link_pairing (H : SimpleGraph V) [DecidableRel H.Adj] (P Q S : Finset V) (e c : ℕ)
    (hPQ : Disjoint P Q) (hS : S ⊆ P ∪ Q) (heven : Even (P.card + Q.card))
    (hSdeg : ∀ a ∈ S, S.card ≤ ((Q \ S).filter (H.Adj a)).card)
    (hPQe : ∀ x ∈ P \ S, (Q.filter fun y => ¬ H.Adj x y).card ≤ e)
    (hQPe : ∀ y ∈ Q \ S, (P.filter fun x => ¬ H.Adj y x).card ≤ e)
    (hPPc : ∀ x ∈ P \ S, (P.filter fun w => ¬ H.Adj x w).card ≤ c)
    (hQQc : ∀ y ∈ Q \ S, (Q.filter fun w => ¬ H.Adj y w).card ≤ c)
    (hP : 2 * e + 1 + 2 * S.card ≤ P.card) (hQ : 2 * e + 1 + 2 * S.card ≤ Q.card)
    (hc : 2 * c + 2 * S.card ≤ P.card + Q.card) :
    ∃ M : Finset (V × V), IsPairing H M ∧ verts M = P ∪ Q ∧
      2 * (M.filter fun q => q.1 ∈ P ∧ q.2 ∈ P).card ≤ P.card + 2 * S.card - Q.card := by
  obtain ⟨M1, hM1, T1, hT1, hT1c, hM1v, hM1o⟩ :=
    exists_pairing_into H S (Q \ S) disjoint_sdiff hSdeg
  set P' := P \ S with hP'
  set Q' := (Q \ S) \ T1 with hQ'
  have hP'P : P' ⊆ P := sdiff_subset
  have hQ'Q : Q' ⊆ Q := sdiff_subset.trans sdiff_subset
  have hT1Q : T1 ⊆ Q := hT1.trans sdiff_subset
  -- cardinalities
  have hsplit : (P ∩ S).card + (Q ∩ S).card = S.card := by
    rw [← card_union_of_disjoint (hPQ.mono inter_subset_left inter_subset_left),
      ← union_inter_distrib_right, inter_eq_right.mpr hS]
  have hP'c : P'.card + (P ∩ S).card = P.card := card_sdiff_add_card_inter P S
  have hQSc : (Q \ S).card + (Q ∩ S).card = Q.card := card_sdiff_add_card_inter Q S
  have hQ'c : Q'.card + T1.card = (Q \ S).card := by
    rw [hQ', linkPairing_card_sdiff hT1]
    have := card_le_card hT1; omega
  have hPQ' : Disjoint P' Q' := hPQ.mono hP'P hQ'Q
  have hdisj : Disjoint (verts M1) (P' ∪ Q') := by
    rw [hM1v]
    refine disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨disjoint_sdiff, ?_⟩, ?_⟩
    · exact disjoint_left.mpr fun w hw hw' => (mem_sdiff.mp (mem_sdiff.mp hw').1).2 hw
    · exact disjoint_union_right.mpr ⟨(hPQ.mono_right hT1Q).symm.mono_right hP'P |>.mono_left
        le_rfl, disjoint_sdiff⟩
  have hverts : S ∪ T1 ∪ (P' ∪ Q') = P ∪ Q := by
    ext w
    simp only [mem_union, hP', hQ', mem_sdiff]
    constructor
    · rintro ((h | h) | h | h)
      · exact mem_union.mp (hS h)
      · exact Or.inr (hT1Q h)
      · exact Or.inl h.1
      · exact Or.inr h.1.1
    · rintro (h | h)
      · by_cases hw : w ∈ S
        · exact Or.inl (Or.inl hw)
        · exact Or.inr (Or.inl ⟨h, hw⟩)
      · by_cases hw : w ∈ S
        · exact Or.inl (Or.inl hw)
        · by_cases hw' : w ∈ T1
          · exact Or.inl (Or.inr hw')
          · exact Or.inr (Or.inr ⟨⟨h, hw⟩, hw'⟩)
  obtain ⟨k, hk⟩ := heven
  have hev : Even (P'.card + Q'.card) := ⟨k - S.card, by omega⟩
  have hM1Q : ∀ q ∈ M1, q.2 ∉ P := fun q hq h =>
    disjoint_left.mp hPQ h (hT1Q (hM1o q hq).2)
  rcases le_or_gt P'.card Q'.card with hle | hlt
  · obtain ⟨Mc, hMc, hMcv, hMco, -⟩ := link_pairing_core H P' Q' e c hPQ' hle hev
      (fun x hx => (card_le_card (filter_subset_filter _ hQ'Q)).trans (hPQe x hx))
      (fun y hy => (card_le_card (filter_subset_filter _ hP'P)).trans
        (hQPe y (sdiff_subset hy)))
      (fun y hy => (card_le_card (filter_subset_filter _ hQ'Q)).trans
        (hQQc y (sdiff_subset hy)))
      (by omega) (by omega)
    refine ⟨M1 ∪ Mc, hM1.union hMc (hMcv ▸ hdisj), by rw [verts_union, hMcv, hM1v, hverts], ?_⟩
    have : (M1 ∪ Mc).filter (fun q => q.1 ∈ P ∧ q.2 ∈ P) = ∅ := by
      refine filter_false_of_mem fun q hq h => ?_
      rcases mem_union.mp hq with h1 | h1
      · exact hM1Q q h1 h.2
      · exact disjoint_left.mp hPQ h.2 (hQ'Q (hMco q h1))
    rw [this, card_empty]; omega
  · obtain ⟨Mc, hMc, hMcv, hMco, hMcc⟩ := link_pairing_core H Q' P' e c hPQ'.symm hlt.le
      (by rwa [add_comm])
      (fun y hy => (card_le_card (filter_subset_filter _ hP'P)).trans
        (hQPe y (sdiff_subset hy)))
      (fun x hx => (card_le_card (filter_subset_filter _ hQ'Q)).trans (hPQe x hx))
      (fun x hx => (card_le_card (filter_subset_filter _ hP'P)).trans (hPPc x hx))
      (by omega) (by omega)
    rw [union_comm] at hMcv
    refine ⟨M1 ∪ Mc, hM1.union hMc (hMcv ▸ hdisj), by rw [verts_union, hMcv, hM1v, hverts], ?_⟩
    have hsub : (M1 ∪ Mc).filter (fun q => q.1 ∈ P ∧ q.2 ∈ P) ⊆
        Mc.filter (fun q => q.1 ∈ P') := by
      intro q hq
      obtain ⟨hq, h1, h2⟩ := mem_filter.mp hq
      rcases mem_union.mp hq with h | h
      · exact absurd h2 (hM1Q q h)
      · refine mem_filter.mpr ⟨h, ?_⟩
        have hv : q.1 ∈ P' ∪ Q' := hMcv ▸ mem_verts.mpr ⟨q, h, Or.inl rfl⟩
        rcases mem_union.mp hv with hv | hv
        · exact hv
        · exact absurd (hQ'Q hv) (disjoint_left.mp hPQ h1)
    have := card_le_card hsub
    have hT1c' := hT1c
    omega

end NashWilliams18
