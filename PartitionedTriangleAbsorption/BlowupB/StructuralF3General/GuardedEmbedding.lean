/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedSupply

/-! # Finite rooted embedding from guarded common-neighbour supply

The roots may lie in the external exclusion set.  Each new vertex avoids that
set, and each inserted edge avoids the physical edge ledger.  No edge between
roots is queried: any required edge there belongs to the supplied initial
partial embedding.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection

variable {W V : Type*} [Fintype W] [DecidableEq W]
  [Fintype V] [DecidableEq V] {t : ℕ}

structure PartialEmbedding (T : SimpleGraph W) (G : SimpleGraph V)
    (B : Finset (Sym2 V)) (U : Finset W) (f : W → V) : Prop where
  injective : ∀ i ∈ U, ∀ j ∈ U, f i = f j → i = j
  edges : ∀ i ∈ U, ∀ j ∈ U, T.Adj i j →
    G.Adj (f i) (f j) ∧ s(f i, f j) ∉ B

theorem guarded_extend_partial (T : SimpleGraph W) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (label : W → Fin t)
    (Allowed : Fin t → Fin t → Prop)
    (hproper : ∀ i j, T.Adj i j → Allowed (label i) (label j))
    (D : ℕ) (a d : ℝ) (hs : GuardedSupply p G Allowed D a)
    (B : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (Fintype.card W : ℝ) + Z.card + D * d < a)
    (U : Finset W) (j : W) (hj : j ∉ U) (f : W → V)
    (hf : PartialEmbedding T G B U f) (hp : ∀ i ∈ U, p (f i) = label i)
    (hparents : (U.filter fun i => T.Adj i j).card ≤ D) :
    ∃ g, PartialEmbedding T G B (insert j U) g ∧
      (∀ i ∈ insert j U, p (g i) = label i) ∧
      (∀ i ∈ U, g i = f i) ∧ g j ∉ Z := by
  let parents := U.filter fun i => T.Adj i j
  let S := parents.image f
  let used := U.image f
  have hS : S.card ≤ D := card_image_le.trans hparents
  have hu : used.card ≤ Fintype.card W := card_image_le.trans (card_le_univ U)
  have huz : ((used ∪ Z).card : ℝ) ≤ (Fintype.card W : ℝ) + Z.card := by
    exact_mod_cast (card_union_le used Z).trans (Nat.add_le_add_right hu _)
  have hguard : ∀ u ∈ S, Allowed (p u) (label j) := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hu
    obtain ⟨hi, hij⟩ := mem_filter.mp hi
    rw [hp i hi]
    exact hproper i j hij
  obtain ⟨w, hpw, hw, hn, hb⟩ := guarded_exists_avoiding p G Allowed D a d hs
    S (used ∪ Z) hS B hB hd (by linarith) (label j) hguard
  have hneq : ∀ i ∈ U, f i ≠ w := by
    intro i hi he
    exact hn (mem_union.mpr (Or.inl (mem_image.mpr ⟨i, hi, he⟩)))
  have hparent : ∀ i ∈ U, T.Adj i j → G.Adj (f i) w ∧ s(f i,w) ∉ B := by
    intro i hi hij
    have hmem : f i ∈ S := mem_image.mpr ⟨i, mem_filter.mpr ⟨hi, hij⟩, rfl⟩
    exact ⟨hw _ hmem, hb _ hmem⟩
  let g := Function.update f j w
  have hkeep : ∀ i ∈ U, g i = f i := by
    intro i hi
    exact Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi)) w f
  have hnew : g j = w := Function.update_self _ _ _
  refine ⟨g, ⟨?_, ?_⟩, ?_, hkeep, ?_⟩
  · intro i hi l hl hil
    rcases mem_insert.mp hi with hij | hiU
    · subst i
      rcases mem_insert.mp hl with hlj | hlU
      · subst l; rfl
      · exact False.elim (hneq l hlU (by simpa only [hnew, hkeep l hlU] using hil.symm))
    · rcases mem_insert.mp hl with hlj | hlU
      · subst l
        exact False.elim (hneq i hiU (by simpa only [hnew, hkeep i hiU] using hil))
      · exact hf.injective i hiU l hlU (by simpa only [hkeep i hiU, hkeep l hlU] using hil)
  · intro i hi l hl hil
    rcases mem_insert.mp hi with hij | hiU
    · subst i
      rcases mem_insert.mp hl with hlj | hlU
      · subst l; exact False.elim (T.irrefl hil)
      · obtain ⟨he, hb'⟩ := hparent l hlU hil.symm
        refine ⟨?_, ?_⟩
        · simpa only [hnew, hkeep l hlU] using he.symm
        · simpa only [hnew, hkeep l hlU, Sym2.eq_swap] using hb'
    · rcases mem_insert.mp hl with hlj | hlU
      · subst l
        simpa only [hkeep i hiU, hnew] using hparent i hiU hil
      · simpa only [hkeep i hiU, hkeep l hlU] using hf.edges i hiU l hlU hil
  · intro i hi
    rcases mem_insert.mp hi with rfl | hi
    · simpa only [hnew] using hpw
    · rw [hkeep i hi]
      exact hp i hi
  · rw [hnew]
    exact fun hz => hn (mem_union.mpr (Or.inr hz))

theorem guarded_exists_embedding (T : SimpleGraph W) [DecidableRel T.Adj]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t) (label : W → Fin t)
    (Allowed : Fin t → Fin t → Prop)
    (hproper : ∀ i j, T.Adj i j → Allowed (label i) (label j))
    (a d : ℝ) (hs : GuardedSupply p G Allowed (Fintype.card W) a)
    (B : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d) (hd : 0 ≤ d)
    (hbudget : (Fintype.card W : ℝ) + Z.card + Fintype.card W * d < a)
    (R : Finset W) (rootMap : W → V) (hroot : PartialEmbedding T G B R rootMap)
    (hlabel : ∀ i ∈ R, p (rootMap i) = label i) :
    ∃ f : W ↪ V, (∀ i, p (f i) = label i) ∧
      (∀ i ∈ R, f i = rootMap i) ∧
      (∀ i j, T.Adj i j → G.Adj (f i) (f j) ∧ s(f i, f j) ∉ B) ∧
      (∀ i, i ∉ R → f i ∉ Z) := by
  have h : ∀ K : Finset W, Disjoint K R →
      ∃ f, PartialEmbedding T G B (R ∪ K) f ∧
        (∀ i ∈ R ∪ K, p (f i) = label i) ∧
        (∀ i ∈ R, f i = rootMap i) ∧ (∀ i ∈ K, f i ∉ Z) := by
    intro K
    induction K using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨rootMap, by simpa using hroot, by simpa using hlabel,
        fun _ _ => rfl, by simp⟩
    | @insert j K hj ih =>
      intro hdis
      have hjR : j ∉ R := (Finset.disjoint_insert_left.mp hdis).1
      obtain ⟨f, hf, hp, hfix, havoid⟩ := ih (Finset.disjoint_insert_left.mp hdis).2
      have hjU : j ∉ R ∪ K := by simpa only [mem_union, not_or] using And.intro hjR hj
      obtain ⟨g, hg, hgp, hkeep, hnew⟩ := guarded_extend_partial T G p label Allowed hproper
        (Fintype.card W) a d hs B Z hB hd hbudget (R ∪ K) j hjU f hf hp
        ((card_filter_le _ _).trans (card_le_univ _))
      have hsets : R ∪ insert j K = insert j (R ∪ K) := by ext; simp
      refine ⟨g, by simpa only [hsets] using hg, by simpa only [hsets] using hgp, ?_, ?_⟩
      · intro i hi
        exact (hkeep i (mem_union_left _ hi)).trans (hfix i hi)
      · intro i hi
        rcases mem_insert.mp hi with rfl | hi
        · exact hnew
        · rw [hkeep i (mem_union_right _ hi)]
          exact havoid i hi
  obtain ⟨f, hf, hp, hfix, havoid⟩ := h (univ \ R) disjoint_sdiff_self_left
  have hU : R ∪ (univ \ R) = univ := union_sdiff_of_subset (subset_univ R)
  refine ⟨⟨f, ?_⟩, ?_, hfix, ?_, ?_⟩
  · intro i j hij
    exact hf.injective i (by rw [hU]; exact mem_univ _) j (by rw [hU]; exact mem_univ _) hij
  · intro i
    exact hp i (by rw [hU]; exact mem_univ _)
  · intro i j hij
    exact hf.edges i (by rw [hU]; exact mem_univ _) j (by rw [hU]; exact mem_univ _) hij
  · intro i hi
    exact havoid i (mem_sdiff.mpr ⟨mem_univ _, hi⟩)

#print axioms guarded_extend_partial
#print axioms guarded_exists_embedding

end PartitionedTriangleAbsorption.StructuralF3General
