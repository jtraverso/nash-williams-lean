/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.NearConsumer
public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedCoverDownConsumer

/-! # Typed nibble and cover-down without exact fractional repair

The positive tolerance is chosen before the graph. A supplied anti-edgeful
reserve supplies the degree gap required by the near-load nibble. The final
consumer still requires a single supplied universal absorber and weights on
the actual main graph. It does not construct either missing input.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/TypedNearConsumer.lean.
Original SHA256: beb054a2cf1724678bebd7366b6f03e15926adcf9cb84ad6c53804ec3759e7e6.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNearConsumer

open Finset TypedNibble TypedCoverDown

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem exists_type_of_load_pos (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) (φ : Finset V → ℝ) {a b : V}
    (hload : 0 < ∑ s ∈ copies p F J with s(a, b) ∈ triEdges s, φ s) :
    ∃ k : Fin t, ({p a, p b, k} : Multiset (Fin t)) ∈ F := by
  obtain ⟨s, hs, -⟩ := exists_ne_zero_of_sum_ne_zero hload.ne'
  obtain ⟨hsc, hab⟩ := mem_filter.mp hs
  have hcopy := mem_copies_iff.mp hsc
  obtain ⟨ha, hb, hne⟩ := mem_triEdges_iff.mp hab
  obtain ⟨c, hac, hbc, rfl⟩ := exists_third_of_card_three hcopy.1.card_eq ha hb hne
  refine ⟨p c, ?_⟩
  rw [← map_three p hne hac hbc]
  exact hcopy.2

/-- The reserve forces a degree gap at every vertex incident to a typeable
main edge. Vertices with no main edges require no population assumption. -/
theorem degree_gap_of_reserve (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (J : SimpleGraph V) [DecidableRel J.Adj] (X : Finset (Sym2 V))
    [DecidableRel (ReserveCoverDown.reserveGraph X).Adj]
    (α : ℝ) (hα : α ≤ 1) (hdis : Disjoint J.edgeFinset X)
    (hres : AntiEdgeful p F (ReserveCoverDown.reserveGraph X) α)
    (htype : ∀ a b, J.Adj a b → ∃ k, ({p a, p b, k} : Multiset (Fin t)) ∈ F) :
    DegBounded J.edgeFinset ((1 - α) * Fintype.card V) := by
  classical
  intro v
  by_cases hempty : Nibble.star J.edgeFinset v = ∅
  · change ((Nibble.star J.edgeFinset v).card : ℝ) ≤ _
    rw [hempty, card_empty, Nat.cast_zero]
    exact mul_nonneg (sub_nonneg.mpr hα) (Nat.cast_nonneg _)
  obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hempty
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp (mem_filter.mp he).2
  have hvu : J.Adj v u := J.mem_edgeFinset.mp (mem_filter.mp he).1
  obtain ⟨k, hk⟩ := htype v u hvu
  let W := univ.filter (fun w => (ReserveCoverDown.reserveGraph X).Adj v w ∧
    (ReserveCoverDown.reserveGraph X).Adj w u ∧ p w = k)
  have hW : α * Fintype.card V ≤ (W.card : ℝ) :=
    hres _ hk _ _ _ rfl v u hvu.ne rfl rfl
  have hc : W.card ≤ (Nibble.star X v).card := by
    apply card_le_card_of_injOn (fun w => s(v, w))
    · intro w hw
      have hadj := (mem_filter.mp hw).2.1
      change s(v, w) ∈ X ∧ v ≠ w at hadj
      exact mem_filter.mpr ⟨hadj.1, by simp⟩
    · intro w _ w' _ heq
      rcases Sym2.eq_iff.mp heq with h | h
      · exact h.2
      · exact h.2.trans h.1
  have hsum : (Nibble.star J.edgeFinset v).card + (Nibble.star X v).card ≤ Fintype.card V := by
    unfold Nibble.star
    rw [← card_union_of_disjoint (hdis.mono (filter_subset _ _) (filter_subset _ _))]
    rw [← filter_union]
    exact Nibble.card_star_le _ _
  have hcR : (W.card : ℝ) ≤ (Nibble.star X v).card := by exact_mod_cast hc
  have hsR : ((Nibble.star J.edgeFinset v).card : ℝ) + (Nibble.star X v).card ≤
      Fintype.card V := by exact_mod_cast hsum
  change ((Nibble.star J.edgeFinset v).card : ℝ) ≤ _
  nlinarith

/-- Typed physical packing from capped near-unit loads and a degree gap. -/
theorem typed_nibble_packing_near (b η ξ : ℝ) (hb : 0 < b) (hη : 0 < η) (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : SimpleGraph V)
        [DecidableRel J.Adj] (φ : Finset V → ℝ),
        (∀ s, IsCopy p F J s → 0 ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
        DegBounded J.edgeFinset ((1 - ξ) * Fintype.card V) →
        (∀ e ∈ J.edgeFinset, |(∑ s ∈ copies p F J with e ∈ triEdges s, φ s) - 1| ≤ δ) →
        ∃ D : Finset (Finset V), ∃ Q : Finset (Sym2 V),
          D ⊆ copies p F J ∧ Q = D.biUnion triEdges ∧ Q ⊆ J.edgeFinset ∧
          IsDecomp p F Q D ∧ HasDecomp p F Q ∧
          DegBounded (J.edgeFinset \ Q) (η * Fintype.card V) := by
  obtain ⟨δ, hδ, hδ1, N, hN⟩ := Nibble.nibble_packing_near b η ξ hb hη hξ
  refine ⟨δ, hδ, hδ1, N, ?_⟩
  intro V _ _ hV t p F J _ φ hw hcap hload
  obtain ⟨P, hP, hdeg⟩ := hN V hV (copies p F J).card (copySystem p F J) J.edgeFinset
    (copyWeights p F J φ)
    (fun i => triEdges_subset_of_isCopy (copySystem_isCopy p F J i))
    (fun i => (hw _ (copySystem_isCopy p F J i)).1)
    (fun i => (hw _ (copySystem_isCopy p F J i)).2) hcap
    (fun e he => by rw [load_copySystem]; exact hload e he)
  rw [edgesOf_eq_biUnion] at hdeg
  have hdec := isDecomp_packedCopies p F J P hP
  refine ⟨packedCopies p F J P, _, ?_, rfl, ?_, hdec, ⟨_, hdec⟩, fun v => hdeg v⟩
  · intro s hs
    obtain ⟨i, -, rfl⟩ := mem_image.mp hs
    exact copySystem_tri_mem p F J i
  · intro e he
    obtain ⟨s, hs, he⟩ := mem_biUnion.mp he
    obtain ⟨i, -, rfl⟩ := mem_image.mp hs
    exact triEdges_subset_of_isCopy (copySystem_isCopy p F J i) he

/-- The same cover-down as Stage28, but exact unit loads are unnecessary.
The absorber and near-unit weights on the main graph remain explicit inputs. -/
theorem typed_cover_down_absorption_near (b α : ℝ) (hb : 0 < b)
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
        (G : SimpleGraph V) [DecidableRel G.Adj] (A X : Finset (Sym2 V))
        [DecidableRel (ReserveCoverDown.reserveGraph X).Adj] (φ : Finset V → ℝ),
        A ⊆ G.edgeFinset → X ⊆ G.edgeFinset → Disjoint A X →
        IsIntDiv p F G.edgeFinset →
        (∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)) →
        AntiEdgeful p F (ReserveCoverDown.reserveGraph X) α →
        (∀ s, IsCopy p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))) s →
          0 ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
        (∀ e ∈ G.edgeFinset \ (A ∪ X),
          |(∑ s ∈ copies p F (G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V)))
            with e ∈ triEdges s, φ s) - 1| ≤ δ) →
        HasDecomp p F G.edgeFinset := by
  obtain ⟨δ, hδ, hδ1, N₀, hN₀⟩ := typed_nibble_packing_near b (α ^ 2 / 256) α hb
    (by positivity) hα0
  refine ⟨δ, hδ, hδ1, max N₀ ⌈256 / α ^ 2⌉₊, ?_⟩
  intro V _ _ hV t p F G _ A X _ φ hA hX hAX hE habs hres hw hload
  classical
  let J := G.deleteEdges ((A ∪ X : Finset (Sym2 V)) : Set (Sym2 V))
  have hJ : J.edgeFinset = G.edgeFinset \ (A ∪ X) := SimpleGraph.edgeFinset_deleteEdges _
  have hpos : ∀ e ∈ J.edgeFinset, 0 < ∑ s ∈ copies p F J with e ∈ triEdges s, φ s := by
    intro e he
    have hh := (abs_le.mp (hload e (hJ ▸ he))).1
    linarith
  have htype : ∀ a b, J.Adj a b → ∃ k, ({p a, p b, k} : Multiset (Fin t)) ∈ F := by
    intro a b hab
    exact exists_type_of_load_pos p F J φ (hpos _ (J.mem_edgeFinset.mpr hab))
  have hdis : Disjoint J.edgeFinset X := by
    rw [hJ]
    exact disjoint_of_subset_right subset_union_right sdiff_disjoint
  have hcap := degree_gap_of_reserve p F J X α hα1 hdis hres htype
  obtain ⟨D, Q, -, -, hQJ, -, hQdec, hdeg⟩ :=
    hN₀ V (le_trans (le_max_left _ _) hV) t p F J φ hw hcap
      (fun e he => hload e (hJ ▸ he))
  rw [hJ] at hQJ hdeg
  let L := (G.edgeFinset \ (A ∪ X)) \ Q
  have hn : 256 / α ^ 2 ≤ (Fintype.card V : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hV)
  have hdegr : DegBounded L (⌈α ^ 2 / 256 * Fintype.card V⌉₊ : ℕ) :=
    fun v => (hdeg v).trans (Nat.le_ceil _)
  have hm := card_le_of_degBounded L
    (not_isDiag_of_mem_edgeFinset G (fun e he => (mem_sdiff.mp (mem_sdiff.mp he).1).1)) _ hdegr
  obtain ⟨hq, hbudget⟩ := schedule_budget α (Fintype.card V) L.card hα0 hα1 hn hm
  refine ReserveCoverDown.hasDecomp_of_sparse_main_packing p F G A X Q α hE hA hX hAX habs
    hres hQJ hQdec ?_ L.card _ _ hq le_rfl hdegr hbudget
  intro a c hac
  exact exists_type_of_load_pos p F J φ (hpos _ (hJ ▸ (mem_sdiff.mp hac).1))

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNearConsumer
