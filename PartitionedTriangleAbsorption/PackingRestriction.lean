/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Restrict a regular almost packing after sparse physical edge deletion

The edge-local loss is bounded by the two endpoint degrees of the deleted
edge set. This is not preservation of the fractional divisibility cone.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingRestriction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

omit [DecidableEq V] in
lemma mem_copies {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} {s : Finset V} : s ∈ copies p F G ↔ IsCopy p F G s := by
  classical
  simp only [copies, mem_filter, mem_powersetCard, subset_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨h.1.card_eq, h⟩⟩

omit [DecidableEq V] in
lemma copies_mono {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G H : SimpleGraph V} (hHG : H ≤ G) : copies p F H ⊆ copies p F G := by
  intro s hs
  obtain ⟨hc, ht⟩ := mem_copies.mp hs
  exact mem_copies.mpr ⟨hc.mono hHG, ht⟩

noncomputable def edgeCopies (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (e : Sym2 V) : Finset (Finset V) :=
  (copies p F G).filter (fun s => e ∈ triEdges s)

lemma edgeCopies_mono {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G H : SimpleGraph V} (hHG : H ≤ G) (e : Sym2 V) :
    edgeCopies p F H e ⊆ edgeCopies p F G e := by
  classical
  exact filter_subset_filter _ (copies_mono hHG)

omit [Fintype V] in
lemma exists_third {s : Finset V} {u v : V} (hs : s.card = 3) (huv : u ≠ v)
    (he : s(u, v) ∈ triEdges s) : ∃ w, u ≠ w ∧ v ≠ w ∧ s = {u,v,w} := by
  have hmem : u ∈ s ∧ v ∈ s := (mk_mem_sym2_iff.mp (mem_filter.mp he).1)
  have hpair : ({u,v} : Finset V) ⊆ s := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hmem.1
    · exact mem_singleton.mp hx ▸ hmem.2
  have hcard : (s \ {u,v}).card = 1 := by
    rw [card_sdiff_of_subset hpair, hs]
    simp [huv]
  obtain ⟨w, hw⟩ := card_eq_one.mp hcard
  have hwm : w ∈ s \ {u,v} := by rw [hw]; simp
  have hne : u ≠ w ∧ v ≠ w := by
    simpa [eq_comm] using (mem_sdiff.mp hwm).2
  refine ⟨w, hne.1, hne.2, ?_⟩
  have hsplit := union_sdiff_of_subset hpair
  rw [hw] at hsplit
  have heq : ({u,v} : Finset V) ∪ {w} = {u,v,w} := by
    ext x
    simp
  rw [heq] at hsplit
  exact hsplit.symm

lemma endpoint_neighbor_count (B : Finset (Sym2 V)) (u : V) :
    (univ.filter (fun w => s(u, w) ∈ B)).card ≤ (B.filter (fun e => u ∈ e)).card := by
  classical
  apply card_le_card_of_injOn (fun w => s(u, w))
  · intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2, by simp⟩
  · intro w _ w' _ he
    rcases Sym2.eq_iff.mp he with h | h
    · exact h.2
    · exact h.2.trans h.1

omit [Fintype V] in
lemma isCopy_of_edges {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G H : SimpleGraph V} {s : Finset V} (hs : IsCopy p F G s)
    (he : ∀ e ∈ triEdges s, e ∈ H.edgeSet) : IsCopy p F H s := by
  refine ⟨⟨?_, hs.1.card_eq⟩, hs.2⟩
  intro a ha b hb hab
  apply (H.mem_edgeSet).mp
  exact he _ (mem_filter.mpr ⟨mk_mem_sym2_iff.mpr ⟨ha,hb⟩,
    by simpa only [Sym2.mk_isDiag_iff] using hab⟩)

theorem lost_copies_card {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G H : SimpleGraph V} (B : Finset (Sym2 V))
    (hremoved : ∀ a b, G.Adj a b → ¬ H.Adj a b → s(a, b) ∈ B)
    {u v : V} (he : H.Adj u v) :
    ((edgeCopies p F G s(u,v) \ edgeCopies p F H s(u,v)).card : ℝ) ≤
      (B.filter (fun e => u ∈ e)).card + (B.filter (fun e => v ∈ e)).card := by
  classical
  let U := univ.filter (fun w => s(u,w) ∈ B)
  let W := univ.filter (fun w => s(v,w) ∈ B)
  have hsub : edgeCopies p F G s(u,v) \ edgeCopies p F H s(u,v) ⊆
      (U ∪ W).image (fun w => ({u,v,w} : Finset V)) := by
    intro s hs
    have hsG := mem_copies.mp (mem_filter.mp (mem_sdiff.mp hs).1).1
    have hse := (mem_filter.mp (mem_sdiff.mp hs).1).2
    obtain ⟨w, huw, hvw, hshape⟩ := exists_third hsG.1.card_eq he.ne hse
    have hbad : s(u,w) ∈ B ∨ s(v,w) ∈ B := by
      by_contra h
      have hnot : s(u,w) ∉ B ∧ s(v,w) ∉ B := by simpa using h
      have hu : G.Adj u w := hsG.1.isClique
        (by simp [hshape]) (by simp [hshape]) huw
      have hv : G.Adj v w := hsG.1.isClique
        (by simp [hshape]) (by simp [hshape]) hvw
      have huH : H.Adj u w := by by_contra h; exact hnot.1 (hremoved _ _ hu h)
      have hvH : H.Adj v w := by by_contra h; exact hnot.2 (hremoved _ _ hv h)
      apply (mem_sdiff.mp hs).2
      refine mem_filter.mpr ⟨mem_copies.mpr (isCopy_of_edges hsG ?_), hse⟩
      intro e he'
      rw [hshape, triEdges_three he.ne huw hvw] at he'
      rcases mem_insert.mp he' with rfl | he'
      · exact (H.mem_edgeSet).mpr he
      rcases mem_insert.mp he' with rfl | he'
      · exact (H.mem_edgeSet).mpr huH
      · rw [mem_singleton.mp he']
        exact (H.mem_edgeSet).mpr hvH
    refine mem_image.mpr ⟨w, ?_, hshape.symm⟩
    simpa [U, W] using hbad
  have hcount := (card_le_card hsub).trans
    (card_image_le.trans (card_union_le U W))
  have hU := endpoint_neighbor_count B u
  have hW := endpoint_neighbor_count B v
  exact_mod_cast hcount.trans (Nat.add_le_add hU hW)

/-- Sparse deletion preserves an almost packing with an explicit edge-local error. -/
theorem regularAlmostPacking_restrict {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (B : Finset (Sym2 V)) (hHG : H ≤ G)
    (hremoved : ∀ a b, G.Adj a b → ¬ H.Adj a b → s(a, b) ∈ B)
    {C ε d : ℝ} (hC : 0 < C) (hn : 0 < Fintype.card V) (hB : DegBounded B d)
    {φ : Finset V → ℝ} (hφ : IsRegularAlmostPacking p F G C ε φ) :
    IsRegularAlmostPacking p F H C (ε + 2 * C * d / Fintype.card V) φ := by
  classical
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hbound : 0 ≤ C / Fintype.card V := (div_pos hC hnR).le
  have hnonneg : ∀ s ∈ copies p F G, 0 ≤ φ s := by
    intro s hs
    exact (one_div_pos.mpr (mul_pos hC hnR)).le.trans (hφ.1 s (mem_copies.mp hs)).1
  refine ⟨?_, ?_⟩
  · intro s hs
    exact hφ.1 s ⟨hs.1.mono hHG, hs.2⟩
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have heH : H.Adj u v := (H.mem_edgeSet).mp (SimpleGraph.mem_edgeFinset.mp he)
      have heG : s(u,v) ∈ G.edgeFinset :=
        SimpleGraph.mem_edgeFinset.mpr ((G.mem_edgeSet).mpr (hHG heH))
      let S := edgeCopies p F G s(u,v)
      let T := edgeCopies p F H s(u,v)
      have hTS : T ⊆ S := edgeCopies_mono hHG _
      have hcard : ((S \ T).card : ℝ) ≤ 2 * d :=
        (lost_copies_card B hremoved heH).trans (by have hu := hB u; have hv := hB v; linarith)
      have hloss : ∑ s ∈ S \ T, φ s ≤ 2 * d * (C / Fintype.card V) := by
        calc
          ∑ s ∈ S \ T, φ s ≤ ∑ _s ∈ S \ T, C / Fintype.card V := by
            apply sum_le_sum
            intro s hs
            exact (hφ.1 s (mem_copies.mp (mem_filter.mp (mem_sdiff.mp hs).1).1)).2
          _ = ((S \ T).card : ℝ) * (C / Fintype.card V) := by simp
          _ ≤ 2 * d * (C / Fintype.card V) := mul_le_mul_of_nonneg_right hcard hbound
      have hsum : (∑ s ∈ S \ T, φ s) + (∑ s ∈ T, φ s) = ∑ s ∈ S, φ s := sum_sdiff hTS
      have hlossNonneg : 0 ≤ ∑ s ∈ S \ T, φ s := by
        apply sum_nonneg
        intro s hs
        exact hnonneg s (mem_filter.mp (mem_sdiff.mp hs).1).1
      have hmass : 1 - ε ≤ ∑ s ∈ S, φ s ∧ ∑ s ∈ S, φ s ≤ 1 := hφ.2 _ heG
      have hfactor : 2 * d * (C / Fintype.card V) = 2 * C * d / Fintype.card V := by ring
      change 1 - (ε + 2 * C * d / Fintype.card V) ≤ ∑ s ∈ T, φ s ∧
        ∑ s ∈ T, φ s ≤ 1
      rw [hfactor] at hloss
      constructor <;> linarith

/-- Consumer for the existing edge-deletion operation, with no extra compatibility axiom. -/
theorem regularAlmostPacking_deleteEdges {p : V → Fin t}
    {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) {C ε d : ℝ} (hC : 0 < C)
    (hn : 0 < Fintype.card V) (hB : DegBounded B d)
    {φ : Finset V → ℝ} (hφ : IsRegularAlmostPacking p F G C ε φ) :
    IsRegularAlmostPacking p F (G.deleteEdges (B : Set (Sym2 V))) C
      (ε + 2 * C * d / Fintype.card V) φ := by
  refine regularAlmostPacking_restrict B (SimpleGraph.deleteEdges_le _) ?_ hC hn hB hφ
  intro a b ha hb
  by_contra h
  exact hb (SimpleGraph.deleteEdges_adj.mpr ⟨ha, h⟩)

omit [Fintype V] [DecidableEq V] in
/-- An explicit scalar allowance for deletion compatible with a target packing error. -/
theorem restriction_error_budget {n C d ε η : ℝ} (hn : 0 < n)
    (hε : ε ≤ η / 2) (hbudget : 4 * C * d ≤ η * n) :
    ε + 2 * C * d / n ≤ η := by
  have hterm : 2 * C * d / n ≤ η / 2 := by
    apply (div_le_iff₀ hn).mpr
    nlinarith
  linarith

end PartitionedTriangleAbsorption.PackingRestriction
