/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.Residual126
public import RequestProject.NW18.Case126.FixerEdges

@[expose] public section

/-!
# The total packing `T₁ ∪ T₂ ∪ Q` (end of the proof of Theorem 12.6)

`T₁` comes from Lemma 15.9 (avoiding the fixer edges `W`), `T₂` from Lemma 15.17 inside
`cleanGraph G A (⋃ T₁) W`, and `Q` is one of the two triangle pairs of the parity-fixer.
`tot_props` collects what is needed to apply Theorem 14.7 to the remaining graph: the union is a
triangle packing covering all edges at `A`, every remaining edge outside `A` is `F₁`-allowed,
the remaining edge set is cross-divisible for `P*`, and the degree of the union is controlled.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V}

/-- The edges of a triangle of `cleanGraph G A C W`. -/
lemma clean_tri_edges {C W : Finset (Sym2 V)} {t : Finset V}
    (ht : (cleanGraph G A C W).IsNClique 3 t) {e : Sym2 V} (he : e ∈ triEdges t) :
    e ∈ G.edgeFinset ∧ e ∉ C ∧ e ∉ W := by
  have := triEdges_subset_of_isNClique ht he
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeFinset] at this
    exact ⟨G.mem_edgeFinset.mpr this.1, this.2.2.2.1, this.2.2.2.2⟩

lemma tot_props (W : Finset (Sym2 V)) (T1 T2 Q : Finset (Finset V))
    (hT1 : IsTrianglePacking G T1) (hT1W : Disjoint (T1.biUnion triEdges) W)
    (hcov1 : ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∉ W → s(u, v) ∈ T1.biUnion triEdges)
    (hsur1 : intSurplus (sideP G p A) (G.edgeFinset \ T1.biUnion triEdges) = 0)
    (hT2 : IsTrianglePacking (cleanGraph G A (T1.biUnion triEdges) W) T2)
    (hT2cov : ∀ x y, (cleanGraph G A (T1.biUnion triEdges) W).Adj x y →
      ¬ AllowedT F1 (p x) (p y) → s(x, y) ∈ T2.biUnion triEdges)
    (hT2cross : ∀ t ∈ T2, ¬ IsInteriorTri (sideP G p A) t)
    (hQ : FixQ G p A (sideP G p A) W Q) :
    IsTrianglePacking G (T1 ∪ T2 ∪ Q) ∧
      (∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ (T1 ∪ T2 ∪ Q).biUnion triEdges) ∧
      (∀ x y, G.Adj x y → s(x, y) ∉ (T1 ∪ T2 ∪ Q).biUnion triEdges → x ∉ A → y ∉ A →
        AllowedT F1 (p x) (p y)) ∧
      intSurplus (sideP G p A) (G.edgeFinset \ (T1 ∪ T2 ∪ Q).biUnion triEdges) = 0 ∧
      (∀ a, (((T1 ∪ T2 ∪ Q).biUnion triEdges).filter (fun e => a ∈ e)).card ≤
        ((T1.biUnion triEdges).filter (fun e => a ∈ e)).card +
        ((T2.biUnion triEdges).filter (fun e => a ∈ e)).card +
        (W.filter (fun e => a ∈ e)).card) := by
  set C1 := T1.biUnion triEdges with hC1
  set C2 := T2.biUnion triEdges with hC2
  set CQ := Q.biUnion triEdges with hCQ
  have hTot : (T1 ∪ T2 ∪ Q).biUnion triEdges = C1 ∪ C2 ∪ CQ := by
    rw [union_biUnion, union_biUnion]
  have hle : cleanGraph G A C1 W ≤ G := fun x y h => h.1
  have hT2G : ∀ t ∈ T2, G.IsNClique 3 t := fun t ht => SimpleGraph.IsNClique.mono hle (hT2.1 t ht)
  have hC2e : ∀ e ∈ C2, e ∈ G.edgeFinset ∧ e ∉ C1 ∧ e ∉ W := by
    intro e he
    obtain ⟨t, ht, het⟩ := mem_biUnion.mp he
    exact clean_tri_edges (hT2.1 t ht) het
  have hC1G : C1 ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT1.1 t ht)
  have hCQW : CQ ⊆ W := hQ.sub
  have hd12 : Disjoint C1 C2 := disjoint_right.mpr fun e he => (hC2e e he).2.1
  have hd1Q : Disjoint C1 CQ := disjoint_of_subset_right hCQW hT1W
  have hd2Q : Disjoint C2 CQ := disjoint_left.mpr fun e he heQ => (hC2e e he).2.2 (hCQW heQ)
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro t ht
    simp only [mem_union] at ht
    rcases ht with (ht | ht) | ht
    exacts [hT1.1 t ht, hT2G t ht, hQ.pack.1 t ht]
  · rw [coe_union, coe_union, Set.pairwiseDisjoint_union, Set.pairwiseDisjoint_union]
    refine ⟨⟨hT1.2, hT2.2, ?_⟩, hQ.pack.2, ?_⟩
    · intro t ht t' ht' _
      exact hd12.mono (subset_biUnion_of_mem triEdges ht) (subset_biUnion_of_mem triEdges ht')
    · intro t ht t' ht' _
      simp only [Set.mem_union, mem_coe] at ht
      rcases ht with ht | ht
      · exact hd1Q.mono (subset_biUnion_of_mem triEdges ht) (subset_biUnion_of_mem triEdges ht')
      · exact hd2Q.mono (subset_biUnion_of_mem triEdges ht) (subset_biUnion_of_mem triEdges ht')
  · intro u v huv hA
    rw [hTot]
    by_cases hW : s(u, v) ∈ W
    · exact mem_union_right _ (hQ.covA u v hW hA)
    · exact mem_union_left _ (mem_union_left _ (hcov1 u v huv hA hW))
  · intro x y hxy hnot hx hy
    rw [hTot] at hnot
    simp only [mem_union, not_or] at hnot
    by_cases hW : s(x, y) ∈ W
    · exact (hQ.rest x y hW hnot.2).2.2
    · by_contra hna
      exact hnot.1.2 (hT2cov x y ⟨hxy, hx, hy, hnot.1.1, hW⟩ hna)
  · rw [hTot]
    have hsub : C2 ∪ CQ ⊆ G.edgeFinset \ C1 := by
      intro e he
      rcases mem_union.mp he with he | he
      · exact mem_sdiff.mpr ⟨(hC2e e he).1, (hC2e e he).2.1⟩
      · exact mem_sdiff.mpr ⟨(hQ.pack.1 _ (mem_biUnion.mp he).choose_spec.1 |>
          triEdges_subset_of_isNClique) (mem_biUnion.mp he).choose_spec.2,
          fun h1 => disjoint_left.mp hd1Q h1 he⟩
    have heq : G.edgeFinset \ (C1 ∪ C2 ∪ CQ) = (G.edgeFinset \ C1) \ (C2 ∪ CQ) := by
      ext e; simp only [mem_sdiff, mem_union]; tauto
    rw [heq, intSurplus_sdiff _ hsub, hsur1, intSurplus_union _ hd2Q,
      intSurplus_biUnion _ T2 (fun t ht => (hT2G t ht).card_eq) hT2.2,
      intSurplus_biUnion _ Q (fun t ht => (hQ.pack.1 t ht).card_eq) hQ.pack.2]
    rw [filter_false_of_mem (fun t ht => hT2cross t ht),
      filter_false_of_mem (fun t ht => hQ.cross t ht)]
    simp
  · intro a
    rw [hTot, filter_union, filter_union]
    refine (card_union_le _ _).trans (add_le_add ((card_union_le _ _).trans le_rfl)
      (card_le_card (filter_subset_filter _ hCQW)))

end NashWilliams18
