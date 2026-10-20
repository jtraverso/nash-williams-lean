/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveIndependentTrialsStage197

/-! # Removing the single possible one-block query witness

Both physical legs of each retained candidate belong to two different
packing triangles. This supplies exact Bernoulli-squared trials.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveTwoBlockTrialsStage198

open Finset

variable {V : Type} [DecidableEq V] {t : ℕ}

theorem shared_block_candidates_le_one (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (u v : V) (huv : u ≠ v) (C : Finset V) :
    (C.filter fun w => ∃ s ∈ D, s(u, w) ∈ triEdges s ∧ s(v, w) ∈ triEdges s).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro w hw z hz
  obtain ⟨s, hs, huw, hvw⟩ := (mem_filter.mp hw).2
  obtain ⟨s', hs', huz, hvz⟩ := (mem_filter.mp hz).2
  obtain ⟨hu, hw, hune⟩ := TypedNibble.mem_triEdges_iff.mp huw
  obtain ⟨hv, _, hvne⟩ := TypedNibble.mem_triEdges_iff.mp hvw
  obtain ⟨hu', hz, hune'⟩ := TypedNibble.mem_triEdges_iff.mp huz
  obtain ⟨hv', _, hvne'⟩ := TypedNibble.mem_triEdges_iff.mp hvz
  have huv_s : s(u, v) ∈ triEdges s := TypedNibble.mem_triEdges_iff.mpr ⟨hu, hv, huv⟩
  have huv_s' : s(u, v) ∈ triEdges s' := TypedNibble.mem_triEdges_iff.mpr ⟨hu', hv', huv⟩
  have heq : s = s' := by
    by_contra hne
    exact disjoint_left.mp (hD.2.1 hs hs' hne) huv_s huv_s'
  subst s'
  have htriple : ({u, v, w} : Finset V) = s := by
    apply eq_of_subset_of_card_le
    · exact insert_subset_iff.mpr ⟨hu, insert_subset_iff.mpr ⟨hv, singleton_subset_iff.mpr hw⟩⟩
    · simp [huv, hune, hvne, (hD.1 s hs).1]
  rw [← htriple] at hz
  have hzw : z = w := by simpa [Ne.symm hune', Ne.symm hvne'] using hz
  exact hzw.symm

theorem two_leg_blocks_card (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (u v w : V)
    (huw : s(u, w) ∈ Q) (hvw : s(v, w) ∈ Q)
    (hseparate : ¬ ∃ s ∈ D, s(u, w) ∈ triEdges s ∧ s(v, w) ∈ triEdges s) :
    (D.filter fun s => s(u, w) ∈ triEdges s ∨ s(v, w) ∈ triEdges s).card = 2 := by
  classical
  rw [← hD.2.2] at huw hvw
  obtain ⟨a, ha, hea⟩ := mem_biUnion.mp huw
  obtain ⟨b, hb, heb⟩ := mem_biUnion.mp hvw
  have hab : a ≠ b := by
    intro heq
    subst b
    exact hseparate ⟨a, ha, hea, heb⟩
  let S := D.filter fun s => s(u, w) ∈ triEdges s ∨ s(v, w) ∈ triEdges s
  have hlo : 2 ≤ S.card := by
    have hsub : ({a, b} : Finset (Finset V)) ⊆ S := by
      intro s hs
      rcases mem_insert.mp hs with rfl | hs
      · exact mem_filter.mpr ⟨ha, Or.inl hea⟩
      · have heq := mem_singleton.mp hs
        subst s
        exact mem_filter.mpr ⟨hb, Or.inr heb⟩
    simpa [hab] using card_le_card hsub
  have hhi : S.card ≤ 2 := by
    have heq : S = (D.filter fun s => s(u, w) ∈ triEdges s) ∪
        (D.filter fun s => s(v, w) ∈ triEdges s) := by
      ext s
      simp only [S, mem_filter, mem_union]
      tauto
    rw [heq]
    exact PackingReserveBlocksStage196.query_uses_at_most_two_blocks p F Q D hD u v w
  exact le_antisymm hhi hlo

theorem extract_two_block_trials (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (u v : V) (huv : u ≠ v) (C : Finset V)
    (hlegs : ∀ w ∈ C, s(u, w) ∈ Q ∧ s(v, w) ∈ Q)
    (hroot : ∀ w ∈ C, w ≠ u ∧ w ≠ v) :
    ∃ I : Finset V, I ⊆ C ∧ C.card ≤ 1 + 3 * I.card ∧
      (∀ w ∈ I, (D.filter fun s => s(u, w) ∈ triEdges s ∨ s(v, w) ∈ triEdges s).card = 2) ∧
      ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
        Disjoint (D.filter fun s => s(u, x) ∈ triEdges s ∨ s(v, x) ∈ triEdges s)
          (D.filter fun s => s(u, y) ∈ triEdges s ∨ s(v, y) ∈ triEdges s) := by
  classical
  let B := C.filter fun w => ∃ s ∈ D, s(u, w) ∈ triEdges s ∧ s(v, w) ∈ triEdges s
  let S := C \ B
  obtain ⟨I, hIS, hcount, hpair⟩ := ReserveIndependentTrialsStage197.extract_query_trials
    p F Q D hD u v S (fun w hw => hroot w (mem_sdiff.mp hw).1)
  have hB : B.card ≤ 1 := shared_block_candidates_le_one p F Q D hD u v huv C
  have hcover : C ⊆ S ∪ B := by
    intro w hw
    by_cases hb : w ∈ B
    · exact mem_union.mpr (Or.inr hb)
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hw, hb⟩))
  have hc := le_trans (card_le_card hcover) (card_union_le S B)
  refine ⟨I, fun w hw => (mem_sdiff.mp (hIS hw)).1, by omega, ?_, hpair⟩
  intro w hw
  have hwS := mem_sdiff.mp (hIS hw)
  have hleg := hlegs w hwS.1
  apply two_leg_blocks_card p F Q D hD u v w hleg.1 hleg.2
  intro h
  exact hwS.2 (mem_filter.mpr ⟨hwS.1, h⟩)


end PartitionedTriangleAbsorption.ReserveTwoBlockTrialsStage198
