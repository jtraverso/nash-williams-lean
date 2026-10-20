/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNearConsumer
public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.PolynomialThreshold

@[expose] public section

/-!
# Typed consumers with explicit thresholds

These are the physical-copy adapter and cover-down proof from the supplied
consumer, now applied to the proved effective nibble. The universal absorber
and the weights on the actual main graph are explicit inputs to this consumer;
they are constructed by the separate host theorems in the final assembly.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer

open Finset TypedNibble TypedCoverDown TypedNearConsumer KeevashQuantitative

noncomputable def coverDownTolerance (α : ℝ) : ℝ :=
  loadTolerance (min (α ^ 2 / 256) (min 1 (α ^ 2)))

noncomputable def coverDownThreshold (b α : ℝ) : ℕ :=
  max (Nibble.packingThreshold b (min (α ^ 2 / 256) (min 1 (α ^ 2))))
    ⌈256 / α ^ 2⌉₊

theorem typed_nibble_packing_near_effective (b η ξ : ℝ) (hb : 0 < b) (hη : 0 < η) (hξ : 0 < ξ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      Nibble.packingThreshold b (min η (min 1 (ξ ^ 2))) ≤ Fintype.card V →
      ∀ (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t))) (J : SimpleGraph V)
        [DecidableRel J.Adj] (φ : Finset V → ℝ),
        (∀ s, IsCopy p F J s → 0 ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
        DegBounded J.edgeFinset ((1 - ξ) * Fintype.card V) →
        (∀ e ∈ J.edgeFinset, |(∑ s ∈ copies p F J with e ∈ triEdges s, φ s) - 1| ≤ loadTolerance (min η (min 1 (ξ ^ 2)))) →
        ∃ D : Finset (Finset V), ∃ Q : Finset (Sym2 V),
          D ⊆ copies p F J ∧ Q = D.biUnion triEdges ∧ Q ⊆ J.edgeFinset ∧
          IsDecomp p F Q D ∧ HasDecomp p F Q ∧
          DegBounded (J.edgeFinset \ Q) (η * Fintype.card V) := by
  have hN := Nibble.nibble_packing_near_effective b η ξ hb hη hξ
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

theorem typed_cover_down_absorption_effective (b α : ℝ) (hb : 0 < b)
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      coverDownThreshold b α ≤ Fintype.card V →
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
            with e ∈ triEdges s, φ s) - 1| ≤ coverDownTolerance α) →
        HasDecomp p F G.edgeFinset := by
  have hN₀ := typed_nibble_packing_near_effective b (α ^ 2 / 256) α hb
    (by positivity) hα0
  have hδ1 : coverDownTolerance α ≤ 1 / 4 := by
    have hζ : 0 < min (α ^ 2 / 256) (min 1 (α ^ 2)) := by positivity
    have hζ1 : min (α ^ 2 / 256) (min 1 (α ^ 2)) ≤ 1 :=
      (min_le_right _ _).trans (min_le_left _ _)
    exact (loadTolerance_le_eighth _ hζ hζ1).trans (by norm_num)
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

#print axioms typed_nibble_packing_near_effective
#print axioms typed_cover_down_absorption_effective

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedEffectiveConsumer
