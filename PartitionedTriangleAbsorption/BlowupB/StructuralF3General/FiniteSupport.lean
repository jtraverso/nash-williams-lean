/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Families
public import PartitionedTriangleAbsorption.SignedHinge.Wedge
public import PartitionedTriangleAbsorption.TypedPieceConditions

/-!
# A universe-independent finite support for a typed piece

The physical vertex type may live in any universe.  Passing to a numbered
finite support places the input of the existing coloured-hub producer in
`Type`, without changing the piece, its type vector or its vertex degrees.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection

variable {W V : Type*} [DecidableEq W] [DecidableEq V] {t : ℕ}

omit [DecidableEq W] in
theorem edgeVec_image_embedding (f : W ↪ V) (p : V → Fin t)
    (E : Finset (Sym2 W)) :
    edgeVec p (E.image (Sym2.map f)) = edgeVec (p ∘ f) E := by
  unfold edgeVec
  rw [sum_image fun a _ b _ h => Sym2.map.injective f.injective h]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => rfl

theorem degVec_image_embedding (f : W ↪ V) (p : V → Fin t)
    (E : Finset (Sym2 W)) (w : W) :
    degVec p (E.image (Sym2.map f)) (f w) = degVec (p ∘ f) E w := by
  unfold degVec
  rw [sum_image fun a _ b _ h => Sym2.map.injective f.injective h]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    funext j
    simp [degContrib, f.injective.eq_iff]

theorem isIntDiv_of_image_embedding (f : W ↪ V) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (E : Finset (Sym2 W))
    (h : IsIntDiv p F (E.image (Sym2.map f))) : IsIntDiv (p ∘ f) F E := by
  refine ⟨?_, fun w => ?_⟩
  · simpa only [edgeVec_image_embedding] using h.1
  · simpa only [degVec_image_embedding, Function.comp_apply] using h.2 (f w)

section Support

variable [Fintype V]

noncomputable def supportEmbedding (P : Finset (Sym2 V)) :
    Fin (vertSet P).card ↪ V :=
  (vertSet P).equivFin.symm.toEmbedding.trans (Function.Embedding.subtype _)

theorem supportEmbedding_mem (P : Finset (Sym2 V)) (w : Fin (vertSet P).card) :
    supportEmbedding P w ∈ vertSet P :=
  ((vertSet P).equivFin.symm w).property

theorem supportEmbedding_surjective (P : Finset (Sym2 V)) {v : V}
    (hv : v ∈ vertSet P) : ∃ w, supportEmbedding P w = v := by
  refine ⟨(vertSet P).equivFin ⟨v, hv⟩, ?_⟩
  simp [supportEmbedding]

noncomputable def compactPiece (P : Finset (Sym2 V)) :
    Finset (Sym2 (Fin (vertSet P).card)) :=
  univ.filter (fun e => Sym2.map (supportEmbedding P) e ∈ P)

theorem compactPiece_image (P : Finset (Sym2 V)) :
    (compactPiece P).image (Sym2.map (supportEmbedding P)) = P := by
  classical
  ext e
  simp only [mem_image, compactPiece, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨e', he', rfl⟩
    exact he'
  · intro he
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨i, hi⟩ := supportEmbedding_surjective P
        (SignedHinge.mem_vertSet.mpr ⟨_, he, Sym2.mem_mk_left a b⟩)
      obtain ⟨j, hj⟩ := supportEmbedding_surjective P
        (SignedHinge.mem_vertSet.mpr ⟨_, he, Sym2.mem_mk_right a b⟩)
      exact ⟨s(i, j), by simpa only [Sym2.map_mk, hi, hj] using he,
        by simp only [Sym2.map_mk, hi, hj]⟩

theorem compactPiece_card (P : Finset (Sym2 V)) : (compactPiece P).card = P.card := by
  have h := congrArg Finset.card (compactPiece_image P)
  rwa [card_image_of_injective _ (Sym2.map.injective (supportEmbedding P).injective)] at h

theorem compactPiece_loopless (P : Finset (Sym2 V))
    (hP : ∀ e ∈ P, ¬ e.IsDiag) : ∀ e ∈ compactPiece P, ¬ e.IsDiag := by
  intro e he
  have h := hP (Sym2.map (supportEmbedding P) e) (mem_filter.mp he).2
  simpa only [Sym2.isDiag_map (supportEmbedding P).injective] using h

theorem compactPiece_isIntDiv (P : Finset (Sym2 V)) (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (hP : IsIntDiv p F P) :
    IsIntDiv (p ∘ supportEmbedding P) F (compactPiece P) := by
  apply isIntDiv_of_image_embedding
  simpa only [compactPiece_image] using hP

theorem compactPiece_incidentLoad (P : Finset (Sym2 V)) (w : Fin (vertSet P).card) :
    incidentLoad (compactPiece P) w = incidentLoad P (supportEmbedding P w) := by
  have h := ColouredHub.incidentLoad_image_apply (supportEmbedding P)
    (supportEmbedding P).injective (compactPiece P) w
  rw [compactPiece_image P] at h
  exact h.symm

#print axioms edgeVec_image_embedding
#print axioms degVec_image_embedding
#print axioms isIntDiv_of_image_embedding
#print axioms supportEmbedding_mem
#print axioms supportEmbedding_surjective
#print axioms compactPiece_image
#print axioms compactPiece_card
#print axioms compactPiece_loopless
#print axioms compactPiece_isIntDiv
#print axioms compactPiece_incidentLoad

end Support

end PartitionedTriangleAbsorption.StructuralF3General
