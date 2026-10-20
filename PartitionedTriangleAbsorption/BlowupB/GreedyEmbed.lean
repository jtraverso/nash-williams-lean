/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.AbsorberHook

/-! # BlowupB.GreedyEmbed — greedy embedding of fresh vertices in nearly complete hosts

A finite set of slots `J`, each with a class `c j`, a set of fixed roots `roots j` and a
symmetric irreflexive *need* relation between slots. If every vertex misses at most `d` allowed
neighbours and every class has more than `|S| + |J| + D(d+1)` vertices, where `D` bounds the
number of roots plus needed partners of a slot, then the slots can be filled injectively with
vertices of their classes, outside `S`, adjacent to their roots and to their needed partners
(`greedy_embed`). Valid for every family.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ} {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Greedy embedding.** -/
theorem greedy_embed {J : Type*} [Fintype J] [DecidableEq J] (need : J → J → Prop)
    [DecidableRel need] (hsymm : ∀ j j', need j j' → need j' j) (hirr : ∀ j, ¬ need j j)
    (c : J → Fin t) (roots : J → Finset V) (S : Finset V) {d D : ℕ}
    (hmiss : ∀ v, missDeg p F G v ≤ d)
    (hD : ∀ j, (roots j).card + (univ.filter (need j)).card ≤ D)
    (hA1 : ∀ j, ∀ v ∈ roots j, AllowedPair F (p v) (c j))
    (hA2 : ∀ j j', need j j' → AllowedPair F (c j') (c j))
    (hcls : ∀ i, S.card + Fintype.card J + D * (d + 1) < (univ.filter fun v => p v = i).card) :
    ∃ f : J → V, Function.Injective f ∧ ∀ j, p (f j) = c j ∧ f j ∉ S ∧
      (∀ v ∈ roots j, G.Adj v (f j)) ∧ ∀ j', need j j' → G.Adj (f j) (f j') := by
  have key : ∀ s : Finset J, ∃ f : J → V, Set.InjOn f s ∧ ∀ j ∈ s, p (f j) = c j ∧ f j ∉ S ∧
      (∀ v ∈ roots j, G.Adj v (f j)) ∧ ∀ j' ∈ s, need j j' → G.Adj (f j) (f j') := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨fun j => (Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) (hcls (c j)))).choose,
        by simp, fun j hj => absurd hj (notMem_empty j)⟩
    | insert a s ha ih =>
      obtain ⟨f, hinj, hf⟩ := ih
      set R : Finset V := roots a ∪ (s.filter (need a)).image f with hR
      have hcompat : ∀ u ∈ R, AllowedPair F (p u) (c a) := by
        intro u hu
        rcases mem_union.mp hu with hu | hu
        · exact hA1 a u hu
        · obtain ⟨j', hj', rfl⟩ := mem_image.mp hu
          obtain ⟨hj's, hneed⟩ := mem_filter.mp hj'
          rw [(hf j' hj's).1]
          exact hA2 a j' hneed
      have hq := NearlyCompleteAbsorber.card_query_ge p F G hmiss R (c a) hcompat
      have hRc : R.card ≤ D := by
        refine (card_union_le _ _).trans ?_
        have h1 : ((s.filter (need a)).image f).card ≤ (univ.filter (need a)).card :=
          card_image_le.trans (card_le_card (filter_subset_filter _ (subset_univ s)))
        have := hD a
        omega
      set bad : Finset V := S ∪ s.image f with hbad
      have hbadc : bad.card ≤ S.card + Fintype.card J :=
        (card_union_le _ _).trans (add_le_add le_rfl (card_image_le.trans (card_le_univ s)))
      have hlt : bad.card <
          (univ.filter fun v => p v = c a ∧ ∀ u ∈ R, G.Adj u v).card := by
        have h1 := hcls (c a)
        have h2 : R.card * (d + 1) ≤ D * (d + 1) := Nat.mul_le_mul_right _ hRc
        omega
      obtain ⟨v, hv, hvb⟩ := exists_mem_notMem_of_card_lt_card hlt
      obtain ⟨hpv, hvR⟩ := (mem_filter.mp hv).2
      have hvS : v ∉ S := fun h => hvb (mem_union_left _ h)
      have hvf : ∀ j ∈ s, f j ≠ v := fun j hj h =>
        hvb (mem_union_right _ (mem_image.mpr ⟨j, hj, h⟩))
      have hne : ∀ j ∈ s, j ≠ a := fun j hj h => ha (h ▸ hj)
      refine ⟨Function.update f a v, ?_, ?_⟩
      · intro j hj j' hj' hjj
        simp only [coe_insert, Set.mem_insert_iff, mem_coe] at hj hj'
        rcases hj with rfl | hj <;> rcases hj' with rfl | hj'
        · rfl
        · rw [Function.update_self, Function.update_of_ne (hne j' hj')] at hjj
          exact absurd hjj.symm (hvf j' hj')
        · rw [Function.update_self, Function.update_of_ne (hne j hj)] at hjj
          exact absurd hjj (hvf j hj)
        · rw [Function.update_of_ne (hne j hj), Function.update_of_ne (hne j' hj')] at hjj
          exact hinj hj hj' hjj
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · rw [Function.update_self]
          refine ⟨hpv, hvS, fun u hu => hvR u (mem_union_left _ hu), fun j' hj' hneed => ?_⟩
          rcases mem_insert.mp hj' with rfl | hj'
          · exact absurd hneed (hirr _)
          · rw [Function.update_of_ne (hne j' hj')]
            exact (hvR (f j') (mem_union_right _
              (mem_image.mpr ⟨j', mem_filter.mpr ⟨hj', hneed⟩, rfl⟩))).symm
        · rw [Function.update_of_ne (hne j hj)]
          obtain ⟨h1, h2, h3, h4⟩ := hf j hj
          refine ⟨h1, h2, h3, fun j' hj' hneed => ?_⟩
          rcases mem_insert.mp hj' with h0 | hj''
          · rw [h0, Function.update_self]
            rw [h0] at hneed
            exact hvR (f j) (mem_union_right _
              (mem_image.mpr ⟨j, mem_filter.mpr ⟨hj, hsymm _ _ hneed⟩, rfl⟩))
          · rw [Function.update_of_ne (hne j' hj'')]
            exact h4 j' hj'' hneed
  obtain ⟨f, hinj, hf⟩ := key univ
  exact ⟨f, fun j j' h => hinj (mem_coe.mpr (mem_univ j)) (mem_coe.mpr (mem_univ j')) h,
    fun j => let ⟨h1, h2, h3, h4⟩ := hf j (mem_univ j)
      ⟨h1, h2, h3, fun j' hn => h4 j' (mem_univ j') hn⟩⟩

end PartitionedTriangleAbsorption.BlowupB
