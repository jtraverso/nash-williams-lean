/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingReserveBlocksStage196

/-! # Disjoint triangle-block trials for one common-neighbour query

This finite extraction supplies independent coordinate sets. It does not
assert a probability tail or construct a simultaneous reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveIndependentTrialsStage197

open Finset

variable {A B : Type} [DecidableEq B]

noncomputable def blocked [DecidableEq A] (S : Finset A) (blocks : A → Finset B)
    (x : A) : Finset A :=
  insert x ((blocks x).biUnion fun b => (S.erase x).filter fun y => b ∈ blocks y)

theorem blocked_card_le [DecidableEq A] (S : Finset A) (blocks : A → Finset B) (x : A)
    (hx : x ∈ S) (hsize : (blocks x).card ≤ 2)
    (hfibre : ∀ b, (S.filter fun y => b ∈ blocks y).card ≤ 2) :
    (blocked S blocks x).card ≤ 3 := by
  classical
  have hsmall : ∀ b ∈ blocks x, ((S.erase x).filter fun y => b ∈ blocks y).card ≤ 1 := by
    intro b hb
    have hmem : x ∈ S.filter (fun y => b ∈ blocks y) := mem_filter.mpr ⟨hx, hb⟩
    have hsub : (S.erase x).filter (fun y => b ∈ blocks y) ⊆
        (S.filter fun y => b ∈ blocks y).erase x := by
      intro y hy
      rcases mem_filter.mp hy with ⟨hy, hby⟩
      exact mem_erase.mpr ⟨(mem_erase.mp hy).1, mem_filter.mpr ⟨(mem_erase.mp hy).2, hby⟩⟩
    have h := card_le_card hsub
    rw [card_erase_of_mem hmem] at h
    have hf := hfibre b
    omega
  have hu : ((blocks x).biUnion fun b => (S.erase x).filter fun y => b ∈ blocks y).card ≤
      (blocks x).card := by
    calc
      _ ≤ ∑ b ∈ blocks x, ((S.erase x).filter fun y => b ∈ blocks y).card := card_biUnion_le
      _ ≤ ∑ _b ∈ blocks x, 1 := sum_le_sum hsmall
      _ = (blocks x).card := by simp
  have hi := card_insert_le x ((blocks x).biUnion fun b =>
    (S.erase x).filter fun y => b ∈ blocks y)
  unfold blocked
  omega

theorem extract_disjoint_blocks (S : Finset A) (blocks : A → Finset B)
    (hsize : ∀ x ∈ S, (blocks x).card ≤ 2)
    (hfibre : ∀ b, (S.filter fun y => b ∈ blocks y).card ≤ 2) :
    ∃ I : Finset A, I ⊆ S ∧ S.card ≤ 3 * I.card ∧
      ∀ x ∈ I, ∀ y ∈ I, x ≠ y → Disjoint (blocks x) (blocks y) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S.Nonempty
    · obtain ⟨x, hx⟩ := hS
      let N := blocked S blocks x
      let T := S \ N
      have hxN : x ∈ N := by simp [N, blocked]
      have hT : T ⊂ S := by
        apply ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset, ?_⟩
        intro heq
        have hxT : x ∈ T := heq.symm ▸ hx
        exact (mem_sdiff.mp hxT).2 hxN
      have hsizeT : ∀ y ∈ T, (blocks y).card ≤ 2 :=
        fun y hy => hsize y (mem_sdiff.mp hy).1
      have hfibreT : ∀ b, (T.filter fun y => b ∈ blocks y).card ≤ 2 := by
        intro b
        exact le_trans (card_le_card (filter_subset_filter _ sdiff_subset)) (hfibre b)
      obtain ⟨I, hIT, hcount, hpair⟩ := ih T hT hsizeT hfibreT
      have hxI : x ∉ I := by
        intro h
        exact (mem_sdiff.mp (hIT h)).2 hxN
      have hdis : ∀ y ∈ I, Disjoint (blocks x) (blocks y) := by
        intro y hy
        apply disjoint_left.mpr
        intro b hbx hby
        have hyT := mem_sdiff.mp (hIT hy)
        have hyx : y ≠ x := by
          intro heq
          exact hxI (heq ▸ hy)
        apply hyT.2
        apply mem_insert_of_mem
        exact mem_biUnion.mpr ⟨b, hbx, mem_filter.mpr ⟨mem_erase.mpr ⟨hyx, hyT.1⟩, hby⟩⟩
      refine ⟨insert x I, insert_subset_iff.mpr ⟨hx, fun y hy => (mem_sdiff.mp (hIT hy)).1⟩, ?_, ?_⟩
      · have hN := blocked_card_le S blocks x hx (hsize x hx) hfibre
        change N.card ≤ 3 at hN
        have hcover : S ⊆ T ∪ N := by
          intro y hy
          by_cases hyN : y ∈ N
          · exact mem_union.mpr (Or.inr hyN)
          · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hy, hyN⟩))
        have hsum := le_trans (card_le_card hcover) (card_union_le T N)
        rw [card_insert_of_notMem hxI]
        omega
      · intro y hy z hz hne
        by_cases hyx : y = x
        · subst y
          exact hdis z ((mem_insert.mp hz).resolve_left (Ne.symm hne))
        · have hyI := (mem_insert.mp hy).resolve_left hyx
          by_cases hzx : z = x
          · subst z
            exact (hdis y hyI).symm
          · exact hpair y hyI z ((mem_insert.mp hz).resolve_left hzx) hne
    · have hempty := not_nonempty_iff_eq_empty.mp hS
      subst S
      exact ⟨∅, by simp, by simp, by simp⟩

theorem extract_query_trials {V : Type} [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    (u v : V) (C : Finset V) (hroot : ∀ w ∈ C, w ≠ u ∧ w ≠ v) :
    ∃ I : Finset V, I ⊆ C ∧ C.card ≤ 3 * I.card ∧
      ∀ x ∈ I, ∀ y ∈ I, x ≠ y →
        Disjoint (D.filter fun s => s(u, x) ∈ triEdges s ∨ s(v, x) ∈ triEdges s)
          (D.filter fun s => s(u, y) ∈ triEdges s ∨ s(v, y) ∈ triEdges s) := by
  classical
  let blocks := fun w => D.filter fun s => s(u, w) ∈ triEdges s ∨ s(v, w) ∈ triEdges s
  apply extract_disjoint_blocks C blocks
  · intro w _hw
    have heq : blocks w = (D.filter fun s => s(u, w) ∈ triEdges s) ∪
        (D.filter fun s => s(v, w) ∈ triEdges s) := by
      ext s
      simp only [blocks, mem_filter, mem_union]
      tauto
    rw [heq]
    exact PackingReserveBlocksStage196.query_uses_at_most_two_blocks p F Q D hD u v w
  · intro s
    by_cases hs : s ∈ D
    · apply PackingReserveBlocksStage196.query_block_fibre_le_two s
        (C.filter fun w => s ∈ blocks w) (hD.1 s hs).1 u v
      · intro w hw
        exact hroot w (mem_filter.mp hw).1
      · intro w hw
        exact (mem_filter.mp (mem_filter.mp hw).2).2
    · have heq : (C.filter fun w => s ∈ blocks w) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact hs (mem_filter.mp (mem_filter.mp hw).2).1
      simp [heq]


end PartitionedTriangleAbsorption.ReserveIndependentTrialsStage197
