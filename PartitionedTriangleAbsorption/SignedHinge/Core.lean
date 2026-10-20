/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Slots

/-! # The physical two-mode absorber from chosen occurrence gadgets and slot hinges

Given chosen occurrence gadgets (`OccGood`), an edge-preserving matching
`μ : positive slots ≃ P ⊕ negative slots`, and for each negative slot `τ` a slot hinge between
the slot triangle of `τ` and the slot triangle of its partner `μ⁻¹ τ` (which share exactly
the base edge), all non-root supports being pairwise disjoint and disjoint from the root
region `Z'`, the edge set

  `X = ⋃ Y ∪ ⋃ W ∪ ⋃ H`

is decomposable, `X ∪ P` is decomposable, and `X` is disjoint from `P`. All edge-disjointness
hypotheses of `two_mode_assembly` are derived here from vertex freshness alone.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ} {p : V → Fin t}
  {F : Finset (Multiset (Fin t))}

omit [Fintype V] in
/-- Inside its four roots, a hinge for `{u,v,w}, {u,v,w'}` can only contain the edge `ww'`. -/
theorem hinge_inside {G : SimpleGraph V} {u v w w' : V} {H : Finset (Sym2 V)}
    (hsub : ∀ e ∈ H, e ∈ G.edgeSet) (hH : IsHinge p F {u, v, w} {u, v, w'} H) :
    ∀ e ∈ H, (∀ x ∈ e, x ∈ ({u, v, w, w'} : Finset V)) → e = s(w, w') := by
  intro e he hR
  have hne := hsub e he
  induction e using Sym2.ind with
  | _ p1 p2 =>
    have h12 : p1 ≠ p2 := G.ne_of_adj hne
    have hS : ¬ (p1 ∈ ({u, v, w} : Finset V) ∧ p2 ∈ ({u, v, w} : Finset V)) := by
      rintro ⟨h1, h2⟩
      have := mem_triEdges_of_endpoints hne (fun x hx => by
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact h1
        · exact h2)
      exact disjoint_left.mp hH.1 he (mem_union_left _ this)
    have hS' : ¬ (p1 ∈ ({u, v, w'} : Finset V) ∧ p2 ∈ ({u, v, w'} : Finset V)) := by
      rintro ⟨h1, h2⟩
      have := mem_triEdges_of_endpoints hne (fun x hx => by
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact h1
        · exact h2)
      exact disjoint_left.mp hH.1 he (mem_union_right _ this)
    have h1 := hR p1 (Sym2.mem_mk_left _ _)
    have h2 := hR p2 (Sym2.mem_mk_right _ _)
    simp only [mem_insert, mem_singleton] at h1 h2 hS hS'
    rcases h1 with rfl | rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl h12
        | exact (hS ⟨by simp, by simp⟩).elim
        | exact (hS' ⟨by simp, by simp⟩).elim
        | rfl
        | exact Sym2.eq_swap

theorem vertSet_biUnion_sub {I : Type*} (s : Finset I) (f : I → Finset (Sym2 V)) {v : V}
    (hv : v ∈ vertSet (s.biUnion f)) : ∃ i ∈ s, v ∈ vertSet (f i) := by
  obtain ⟨e, he, hve⟩ := mem_vertSet.mp hv
  obtain ⟨i, hi, hei⟩ := mem_biUnion.mp he
  exact ⟨i, hi, mem_vertSet.mpr ⟨e, hei, hve⟩⟩

variable {O : Type*} [Fintype O] [DecidableEq O]

omit [DecidableEq O] in
/-- **Core physical absorber.** -/
theorem core_absorber {G : SimpleGraph V} {Z' : Finset V} (D : OccData V O)
    (h : ∀ o, OccGood p F G Z' D o)
    (hF : ∀ o o', o ≠ o' → Disjoint (D.fresh o) (D.fresh o'))
    (pos : O → Prop) [DecidablePred pos] (P : Finset (Sym2 V))
    (hPZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z')
    (μ : {σ : O × Fin 3 // pos σ.1} ≃ {f // f ∈ P} ⊕ {τ : O × Fin 3 // ¬ pos τ.1})
    (hμ : ∀ σ, Sum.elim (fun f => f.1) (fun τ => s(D.bu τ.1, D.bv τ.1)) (μ σ) =
      s(D.bu σ.1, D.bv σ.1))
    (Hs : {τ : O × Fin 3 // ¬ pos τ.1} → Finset (Sym2 V))
    (hs1 : ∀ τ, ∀ e ∈ Hs τ, e ∈ G.edgeSet)
    (hs2 : ∀ τ, IsHinge p F {D.bu τ.1, D.bv τ.1, D.ap τ.1}
      {D.bu τ.1, D.bv τ.1, D.ap (μ.symm (Sum.inr τ)).1} (Hs τ))
    (hs3 : ∀ τ, Disjoint (vertSet (Hs τ) \
      {D.bu τ.1, D.bv τ.1, D.ap τ.1, D.ap (μ.symm (Sum.inr τ)).1}) (Z' ∪ univ.biUnion D.fresh))
    (hs4 : ∀ τ τ', τ ≠ τ' →
      Disjoint (vertSet (Hs τ) \
        {D.bu τ.1, D.bv τ.1, D.ap τ.1, D.ap (μ.symm (Sum.inr τ)).1})
      (vertSet (Hs τ') \
        {D.bu τ'.1, D.bv τ'.1, D.ap τ'.1, D.ap (μ.symm (Sum.inr τ')).1})) :
    HasDecomp p F (univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs) ∧
      HasDecomp p F (univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs ∪ P) ∧
      Disjoint (univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs) P ∧
      (∀ e ∈ univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs, e ∈ G.edgeSet) ∧
      vertSet (univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs) ⊆
        Z' ∪ univ.biUnion D.fresh ∪ univ.biUnion (fun τ => vertSet (Hs τ) \
          {D.bu τ.1, D.bv τ.1, D.ap τ.1, D.ap (μ.symm (Sum.inr τ)).1}) ∧
      univ.biUnion D.core ∪ univ.biUnion D.wedge ∪ univ.biUnion Hs ⊆
        univ.biUnion (fun o => D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)}) ∪
          univ.biUnion Hs := by
  classical
  -- notation
  set pt : {τ : O × Fin 3 // ¬ pos τ.1} → O × Fin 3 := fun τ => (μ.symm (Sum.inr τ)).1
    with hpt
  have hpt_pos : ∀ τ, pos (pt τ).1 := fun τ => (μ.symm (Sum.inr τ)).2
  set R : {τ : O × Fin 3 // ¬ pos τ.1} → Finset V :=
    fun τ => {D.bu τ.1, D.bv τ.1, D.ap τ.1, D.ap (pt τ)} with hR
  set FS : {τ : O × Fin 3 // ¬ pos τ.1} → Finset V := fun τ => vertSet (Hs τ) \ R τ with hFS
  -- basic facts
  have fresh_eq : ∀ {o o' : O} {v : V}, v ∈ D.fresh o → v ∈ D.fresh o' → o = o' := by
    intro o o' v h1 h2
    by_contra hne
    exact disjoint_left.mp (hF o o' hne) h1 h2
  have ap_ne_pt : ∀ τ, D.ap τ.1 ≠ D.ap (pt τ) := by
    intro τ he
    have := D.ap_inj h hF he
    exact τ.2 (this ▸ hpt_pos τ)
  have base_pt : ∀ τ, s(D.bu (pt τ), D.bv (pt τ)) = s(D.bu τ.1, D.bv τ.1) := by
    intro τ
    have := hμ (μ.symm (Sum.inr τ))
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  have R_sub : ∀ τ, R τ ⊆ Z' ∪ univ.biUnion D.fresh := by
    intro τ v hv
    simp only [hR, mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact mem_union_left _ (D.bu_Z' h _)
    · exact mem_union_left _ (D.bv_Z' h _)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨_, mem_univ _, D.ap_fresh h _⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨_, mem_univ _, D.ap_fresh h _⟩)
  have hs_vert : ∀ τ, vertSet (Hs τ) ⊆ R τ ∪ FS τ := by
    intro τ v hv
    by_cases hr : v ∈ R τ
    · exact mem_union_left _ hr
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hv, hr⟩)
  have FS_out : ∀ τ {v : V}, v ∈ FS τ → v ∉ Z' ∪ univ.biUnion D.fresh := fun τ v hv =>
    disjoint_left.mp (hs3 τ) hv
  -- endpoints of a slot hinge inside a region avoiding its fresh part lie in its roots
  have to_R : ∀ τ {v : V}, v ∈ vertSet (Hs τ) → v ∈ Z' ∪ univ.biUnion D.fresh → v ∈ R τ := by
    intro τ v hv hZ
    rcases mem_union.mp (hs_vert τ hv) with h' | h'
    · exact h'
    · exact absurd hZ (FS_out τ h')
  have inside : ∀ τ, ∀ e ∈ Hs τ, (∀ v ∈ e, v ∈ R τ) → e = s(D.ap τ.1, D.ap (pt τ)) :=
    fun τ => hinge_inside (hs1 τ) (hs2 τ)
  have blk_vert : ∀ o {v : V},
      v ∈ vertSet (D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)}) → v ∈ Z' ∨ v ∈ D.fresh o := by
    intro o v hv
    rcases mem_union.mp (D.block_vertSet h o hv) with h' | h'
    · exact Or.inl ((h o).roots h')
    · exact Or.inr h'
  -- distinctness for the slot hinges
  have hdist : ∀ τ, D.bu τ.1 ≠ D.bv τ.1 ∧ D.bu τ.1 ≠ D.ap τ.1 ∧ D.bv τ.1 ≠ D.ap τ.1 ∧
      D.bu τ.1 ≠ D.ap (pt τ) ∧ D.bv τ.1 ≠ D.ap (pt τ) ∧ D.ap τ.1 ≠ D.ap (pt τ) := fun τ =>
    ⟨D.bu_ne_bv h _, D.bu_ne_ap h _ _, D.bv_ne_ap h _ _, D.bu_ne_ap h _ _, D.bv_ne_ap h _ _,
      ap_ne_pt τ⟩
  obtain ⟨hdA, hdB, hdis⟩ := two_mode_assembly (p := p) (F := F) pos Prod.fst P D.core
    D.wedge Hs μ
    (fun o => by rw [D.block_eq h o]; exact (h o).dec_block)
    (fun o => (h o).dec_core)
    (fun τ => by
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hdist τ
      have := (hs2 τ).2.1
      rwa [triEdges_sdiff_apex d1 d2 d3 d4 d5 d6] at this)
    (fun τ => by
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hdist τ
      have := (hs2 τ).2.2
      rw [triEdges_sdiff_apex d1 d4 d5 d2 d3 (Ne.symm d6),
        ← wedge_eq_of_sym2_eq _ (base_pt τ)] at this
      exact this)
    (fun f => by
      set σ := (μ.symm (Sum.inl f)).1 with hσ
      have hb : f.1 = s(D.bu σ, D.bv σ) := by
        have := hμ (μ.symm (Sum.inl f))
        rwa [Equiv.apply_symm_apply] at this
      have hc := D.tri_copy h σ
      have hE : insert f.1 (D.wedge σ) = triEdges (D.tri σ) := by
        rw [hb, OccData.tri, triEdges_three (D.bu_ne_bv h σ) (D.bu_ne_ap h σ σ)
          (D.bv_ne_ap h σ σ)]
        rfl
      rw [hE]
      exact hasDecomp_triEdges ⟨hc.1.card_eq, hc.2⟩)
    (fun σ => D.core_wedge_disj h σ)
    (fun σ σ' hne _ => D.wedge_disj h hF hne)
    (fun o o' hne => by
      rw [D.block_eq h o, D.block_eq h o']
      refine disjoint_of_vertSet Z' (fun v h1 h2 => ?_) (D.block_no_inside h o)
      rcases blk_vert o h1 with h1 | h1
      · exact h1
      · rcases blk_vert o' h2 with h2 | h2
        · exact h2
        · exact absurd (fresh_eq h1 h2) hne)
    (fun τ o => by
      rw [D.block_eq h o, disjoint_left]
      intro e he hb
      have hRe : ∀ v ∈ e, v ∈ R τ := fun v hv => by
        refine to_R τ (mem_vertSet_of_mem he hv) ?_
        rcases blk_vert o (mem_vertSet_of_mem hb hv) with h' | h'
        · exact mem_union_left _ h'
        · exact mem_union_right _ (mem_biUnion.mpr ⟨_, mem_univ _, h'⟩)
      have hee := inside τ e he hRe
      subst hee
      have k1 := blk_vert o (mem_vertSet_of_mem hb (Sym2.mem_mk_left _ _))
      have k2 := blk_vert o (mem_vertSet_of_mem hb (Sym2.mem_mk_right _ _))
      rcases k1 with k1 | k1
      · exact D.ap_not_Z' h _ k1
      rcases k2 with k2 | k2
      · exact D.ap_not_Z' h _ k2
      have e1 := fresh_eq (D.ap_fresh h τ.1) k1
      have e2 := fresh_eq (D.ap_fresh h (pt τ)) k2
      exact τ.2 (by rw [e1, ← e2]; exact hpt_pos τ))
    (fun τ τ' hne => by
      rw [disjoint_left]
      intro e he he'
      have toR : ∀ {τ₁ τ₂ : {τ : O × Fin 3 // ¬ pos τ.1}}, τ₁ ≠ τ₂ → e ∈ Hs τ₁ →
          e ∈ Hs τ₂ → ∀ v ∈ e, v ∈ R τ₁ := by
        intro τ₁ τ₂ h12 e1 e2 v hv
        rcases mem_union.mp (hs_vert τ₁ (mem_vertSet_of_mem e1 hv)) with h' | h'
        · exact h'
        · exfalso
          rcases mem_union.mp (hs_vert τ₂ (mem_vertSet_of_mem e2 hv)) with h'' | h''
          · exact FS_out τ₁ h' (R_sub τ₂ h'')
          · exact disjoint_left.mp (hs4 τ₁ τ₂ h12) h' h''
      have q1 := inside τ e he (toR hne he he')
      have q2 := inside τ' e he' (toR (Ne.symm hne) he' he)
      rw [q1] at q2
      rcases Sym2.eq_iff.mp q2 with ⟨r1, -⟩ | ⟨r1, -⟩
      · exact hne (Subtype.ext (D.ap_inj h hF r1))
      · have := D.ap_inj h hF r1
        exact τ.2 (this ▸ hpt_pos τ'))
    (fun o => by
      rw [D.block_eq h o, disjoint_left]
      intro e he hP
      exact D.block_no_inside h o e he (hPZ e hP))
    (fun τ => by
      rw [disjoint_left]
      intro e he hP
      have hRe : ∀ v ∈ e, v ∈ R τ := fun v hv =>
        to_R τ (mem_vertSet_of_mem he hv) (mem_union_left _ (hPZ e hP v hv))
      have hee := inside τ e he hRe
      subst hee
      exact D.ap_not_Z' h _ (hPZ _ hP _ (Sym2.mem_mk_left _ _)))
  refine ⟨hdA, hdB, hdis, ?_, ?_, ?_⟩
  · intro e he
    simp only [mem_union, mem_biUnion, mem_univ, true_and] at he
    rcases he with (⟨o, he⟩ | ⟨σ, he⟩) | ⟨τ, he⟩
    · exact (h o).sub e (D.core_subset o he)
    · exact D.wedge_sub h σ e he
    · exact hs1 τ e he
  · intro v hv
    rw [vertSet_union, vertSet_union] at hv
    simp only [mem_union] at hv
    rcases hv with (hv | hv) | hv
    · obtain ⟨o, -, hv⟩ := vertSet_biUnion_sub _ _ hv
      have := blk_vert o (vertSet_mono ((D.core_subset o).trans subset_union_left) hv)
      rcases this with h' | h'
      · exact mem_union_left _ (mem_union_left _ h')
      · exact mem_union_left _ (mem_union_right _ (mem_biUnion.mpr ⟨o, mem_univ _, h'⟩))
    · obtain ⟨σ, -, hv⟩ := vertSet_biUnion_sub _ _ hv
      have := D.wedge_vertSet σ hv
      simp only [mem_insert, mem_singleton] at this
      rcases this with rfl | rfl | rfl
      · exact mem_union_left _ (mem_union_left _ (D.bu_Z' h σ))
      · exact mem_union_left _ (mem_union_left _ (D.bv_Z' h σ))
      · exact mem_union_left _ (mem_union_right _
          (mem_biUnion.mpr ⟨σ.1, mem_univ _, D.ap_fresh h σ⟩))
    · obtain ⟨τ, -, hv⟩ := vertSet_biUnion_sub _ _ hv
      rcases mem_union.mp (hs_vert τ hv) with h' | h'
      · rcases mem_union.mp (R_sub τ h') with h'' | h''
        · exact mem_union_left _ (mem_union_left _ h'')
        · exact mem_union_left _ (mem_union_right _ h'')
      · exact mem_union_right _ (mem_biUnion.mpr ⟨τ, mem_univ _, h'⟩)
  · intro e he
    simp only [mem_union, mem_biUnion, mem_univ, true_and] at he ⊢
    rcases he with (⟨o, he⟩ | ⟨σ, he⟩) | ⟨τ, he⟩
    · exact Or.inl ⟨o, Or.inl (D.core_subset o he)⟩
    · refine Or.inl ⟨σ.1, ?_⟩
      have hw : e ∈ localBlock Prod.fst D.core D.wedge σ.1 :=
        mem_union_right _ (mem_biUnion.mpr ⟨σ, by simp, he⟩)
      rw [D.block_eq h] at hw
      simp only [mem_union, mem_insert, mem_singleton] at hw ⊢
      exact hw
    · exact Or.inr ⟨τ, he⟩

end PartitionedTriangleAbsorption.SignedHinge
