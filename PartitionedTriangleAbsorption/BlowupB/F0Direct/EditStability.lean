/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkCounts
import PartitionedTriangleAbsorption.PhysicalHingeSupply.Template

/-!
# Edit distance under restriction and sparse deletion

These are finite set estimates for unordered physical edges.  Restriction of
vertices costs only pairs incident with a removed vertex.  A balanced cut on
the smaller set extends to a balanced cut on the larger set.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks PhysicalHingeSupply

variable {V W : Type*} [Fintype V] [DecidableEq V] [DecidableEq W]

theorem mem_triEdges_mk {D : Finset V} {u v : V} :
    s(u,v) ∈ triEdges D ↔ u ∈ D ∧ v ∈ D ∧ u ≠ v := by
  simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
  tauto

private def differences {U : Type*} [DecidableEq U] (E H : Finset U) : Finset U :=
  (E \ H) ∪ (H \ E)

private theorem differences_card (E H : Finset (Sym2 V)) :
    (differences E H).card = editDistance E H := by
  rw [differences, card_union_of_disjoint]
  · rfl
  · apply disjoint_left.mpr
    intro e he hh
    exact (mem_sdiff.mp he).2 (mem_sdiff.mp hh).1

theorem editDistance_le_restrict_delete
    (E H Q Q' B : Finset (Sym2 V)) (hE : E ⊆ Q) (hH : H ⊆ Q) :
    editDistance E H ≤ editDistance ((E \ B) ∩ Q') (H ∩ Q') +
      (Q \ Q').card + B.card := by
  have hs : differences E H ⊆
      (differences ((E \ B) ∩ Q') (H ∩ Q') ∪ (Q \ Q')) ∪ B := by
    intro e he
    simp only [differences, mem_union, mem_sdiff, mem_inter] at he ⊢
    by_cases hb : e ∈ B
    · exact Or.inr hb
    · by_cases hq : e ∈ Q'
      · left; left
        rcases he with he | he
        · exact Or.inl ⟨⟨⟨he.1, hb⟩, hq⟩, fun hh => he.2 hh.1⟩
        · exact Or.inr ⟨⟨he.1, hq⟩, fun hh => he.2 hh.1.1⟩
      · left; right
        exact ⟨he.elim (fun he => hE he.1) (fun he => hH he.1), hq⟩
  have hc := (card_le_card hs).trans (card_union_le _ _)
  have hc' := card_union_le (differences ((E \ B) ∩ Q') (H ∩ Q')) (Q \ Q')
  rw [differences_card] at hc hc'
  omega

theorem editDistance_map (f : W ↪ V) (E H : Finset (Sym2 W)) :
    editDistance (E.map (edgeEmb f)) (H.map (edgeEmb f)) = editDistance E H := by
  simp only [editDistance, ← map_sdiff, card_map]

theorem cliqueModel_map (f : W ↪ V) (D X : Finset W) :
    cliqueModel (D.map f) (X.map f) = (cliqueModel D X).map (edgeEmb f) := by
  simp only [cliqueModel, ← map_sdiff, PhysicalHingeSupply.triEdges_map, map_union]

theorem bipartiteModel_map (f : W ↪ V) (D X : Finset W) :
    bipartiteModel (D.map f) (X.map f) = (bipartiteModel D X).map (edgeEmb f) := by
  rw [bipartiteModel, cliqueModel_map, PhysicalHingeSupply.triEdges_map, ← map_sdiff]
  rfl

theorem balanced_extension {D D' X' : Finset V} (hD : D' ⊆ D)
    (hX : X' ⊆ D') (hbal : X'.card = D'.card / 2) :
    ∃ X ⊆ D, X.card = D.card / 2 ∧ X ∩ D' = X' := by
  have hc := card_le_card hD
  have hr : D.card / 2 - X'.card ≤ (D \ D').card := by
    rw [card_sdiff_of_subset hD, hbal]
    omega
  obtain ⟨Z, hZ, hZc⟩ := exists_subset_card_eq hr
  refine ⟨X' ∪ Z, union_subset (hX.trans hD) (hZ.trans sdiff_subset), ?_, ?_⟩
  · have hd : Disjoint X' Z := by
      apply disjoint_left.mpr
      intro v hv hz
      exact (mem_sdiff.mp (hZ hz)).2 (hX hv)
    rw [card_union_of_disjoint hd, hZc, hbal]
    omega
  · ext v
    simp only [mem_inter, mem_union]
    constructor
    · rintro ⟨hv | hz, hD'⟩
      · exact hv
      · exact False.elim ((mem_sdiff.mp (hZ hz)).2 hD')
    · intro hv
      exact ⟨Or.inl hv, hX hv⟩

theorem cliqueModel_inter {D D' X X' : Finset V}
    (hD : D' ⊆ D) (hX : X ⊆ D) (hXX : X ∩ D' = X') :
    cliqueModel D X ∩ triEdges D' = cliqueModel D' X' := by
  subst X'
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    simp only [cliqueModel, mem_inter, mem_union, mem_triEdges_mk, mem_sdiff]
    constructor
    · rintro ⟨huv | huv, hd⟩
      · exact Or.inl ⟨⟨huv.1, hd.1⟩, ⟨huv.2.1, hd.2.1⟩, huv.2.2⟩
      · exact Or.inr ⟨⟨hd.1, fun hu => huv.1.2 hu.1⟩,
          ⟨hd.2.1, fun hv => huv.2.1.2 hv.1⟩, huv.2.2⟩
    · rintro (huv | huv)
      · exact ⟨Or.inl ⟨huv.1.1, huv.2.1.1, huv.2.2⟩,
          huv.1.2, huv.2.1.2, huv.2.2⟩
      · exact ⟨Or.inr ⟨⟨hD huv.1.1, fun hu => huv.1.2 ⟨hu, huv.1.1⟩⟩,
          ⟨hD huv.2.1.1, fun hv => huv.2.1.2 ⟨hv, huv.2.1.1⟩⟩, huv.2.2⟩,
          huv.1.1, huv.2.1.1, huv.2.2⟩

theorem bipartiteModel_inter {D D' X X' : Finset V}
    (hD : D' ⊆ D) (hX : X ⊆ D) (hXX : X ∩ D' = X') :
    bipartiteModel D X ∩ triEdges D' = bipartiteModel D' X' := by
  have hc := cliqueModel_inter hD hX hXX
  have ht := WalkSupply.triEdges_mono hD
  ext e
  simp only [bipartiteModel, mem_inter, mem_sdiff]
  constructor
  · rintro ⟨⟨he, hn⟩, hd⟩
    refine ⟨hd, ?_⟩
    intro hc'
    have : e ∈ cliqueModel D X ∩ triEdges D' := hc.symm ▸ hc'
    exact hn (mem_inter.mp this).1
  · rintro ⟨hd, hn⟩
    refine ⟨⟨ht hd, ?_⟩, hd⟩
    intro hx
    exact hn (hc ▸ mem_inter.mpr ⟨hx, hd⟩)

theorem card_lost_pairs {D D' : Finset V} (hD : D' ⊆ D) :
    (triEdges D \ triEdges D').card ≤ (D \ D').card * D.card := by
  have hs : triEdges D \ triEdges D' ⊆
      ((D \ D') ×ˢ D).image (fun uv => s(uv.1, uv.2)) := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨he, hn⟩ := mem_sdiff.mp he
      obtain ⟨hu, hv, huv⟩ := mem_triEdges_mk.mp he
      by_cases hu' : u ∈ D'
      · have hv' : v ∉ D' := fun hv' => hn (mem_triEdges_mk.mpr ⟨hu', hv', huv⟩)
        exact mem_image.mpr ⟨(v,u), mem_product.mpr ⟨mem_sdiff.mpr ⟨hv,hv'⟩,hu⟩,
          Sym2.eq_swap⟩
      · exact mem_image.mpr ⟨(u,v), mem_product.mpr ⟨mem_sdiff.mpr ⟨hu,hu'⟩,hv⟩,rfl⟩
  exact (card_le_card hs).trans (card_image_le.trans (by rw [card_product]))

#print axioms editDistance_le_restrict_delete
#print axioms balanced_extension
#print axioms card_lost_pairs

end PartitionedTriangleAbsorption.BlowupB.F0Direct
