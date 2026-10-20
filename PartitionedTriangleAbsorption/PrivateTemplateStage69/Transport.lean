/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ClassHingeDeletionStage69
public import PartitionedTriangleAbsorption.SignedAbsorberAPIStage57

/-! # Transport and promotion lemmas for structural private templates

* `isTypedTri_F3_of_proper`, `isDecomp_F3_of_proper`: **promotion**. If every edge of `E`
  joins two distinct structural classes, then every triangle of any decomposition of `E`
  (for any labelling and any type family) has three distinct classes, so the *same*
  triangle family is a structural `F3` decomposition. Nothing about coarse labels is used.
* `isIntDiv_map`: structural divisibility moves along a vertex embedding.
* `hasDecomp_comap`: a decomposition of an embedded edge set pulls back to the source,
  so the finite support of an absorber can be extracted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplateStage69

open Finset TypedApplicationLinks PhysicalHingeSupply

section Promotion

variable {V : Type*} [DecidableEq V]

/-- Every vertex of a typed triangle lies on one of its edges. -/
theorem exists_edge_of_mem {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {s : Finset V} (hs : IsTypedTri p F s) {a : V} (ha : a ∈ s) :
    ∃ b, b ≠ a ∧ s(a, b) ∈ triEdges s := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hs.1
  simp only [mem_insert, mem_singleton] at ha
  rcases ha with rfl | rfl | rfl
  · exact ⟨y, Ne.symm hxy, by simp [triEdges, hxy]⟩
  · exact ⟨x, hxy, by simp [triEdges, Ne.symm hxy]⟩
  · exact ⟨x, hxz, by simp [triEdges, Ne.symm hxz]⟩

/-- **Promotion of one triangle.** A 3-set whose three edges join distinct classes is a
structural `F3` triangle. -/
theorem isTypedTri_F3_of_proper (cls : V → Fin 4) {s : Finset V} (hs : s.card = 3)
    (hprop : ∀ a b, s(a, b) ∈ triEdges s → cls a ≠ cls b) : IsTypedTri cls F3 s := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := card_eq_three.mp hs
  refine ⟨hs, ?_⟩
  have h1 := hprop x y (by simp [triEdges, hxy])
  have h2 := hprop x z (by simp [triEdges, hxz])
  have h3 := hprop y z (by simp [triEdges, hyz])
  have hval : ({x, y, z} : Finset V).val.map cls = {cls x, cls y, cls z} := by
    simp [hxy, hxz, hyz]
  rw [hval]
  exact ClassCertificate.distinct_mem_F3 _ _ _ h1 h2 h3

/-- **Promotion of decompositions.** If every edge of `E` is properly coloured by the
structural classes, any decomposition of `E` (for any labelling `p` and type family `F`)
is, triangle by triangle, a structural `F3` decomposition. -/
theorem isDecomp_F3_of_proper {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (cls : V → Fin 4) {E : Finset (Sym2 V)} {D : Finset (Finset V)}
    (hD : IsDecomp p F E D) (hE : ∀ a b, s(a, b) ∈ E → cls a ≠ cls b) :
    IsDecomp cls F3 E D := by
  obtain ⟨hT, hP, hU⟩ := hD
  refine ⟨fun s hs => isTypedTri_F3_of_proper cls (hT s hs).1 fun a b hab => ?_, hP, hU⟩
  exact hE a b (hU ▸ mem_biUnion.mpr ⟨s, hs, hab⟩)

theorem hasDecomp_F3_of_proper {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (cls : V → Fin 4) {E : Finset (Sym2 V)} (hD : HasDecomp p F E)
    (hE : ∀ a b, s(a, b) ∈ E → cls a ≠ cls b) : HasDecomp cls F3 E := by
  obtain ⟨D, hD⟩ := hD
  exact ⟨D, isDecomp_F3_of_proper cls hD hE⟩

end Promotion

section Embedding

variable {W V : Type*} [DecidableEq W] [DecidableEq V] {t : ℕ}

omit [DecidableEq W] [DecidableEq V] in
theorem pairVec_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) (e : Sym2 W) :
    pairVec pV (edgeEmb f e) = pairVec pW e := by
  induction e using Sym2.ind with
  | _ a b => simp [edgeEmb, pairVec, hp]

theorem degContrib_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) (w : W) (e : Sym2 W) :
    degContrib pV (f w) (edgeEmb f e) = degContrib pW w e := by
  induction e using Sym2.ind with
  | _ a b => simp [edgeEmb, degContrib, hp, f.injective.eq_iff]

omit [DecidableEq W] in
theorem degContrib_map_outside (f : W ↪ V) (pV : V → Fin t) {v : V}
    (hv : ∀ w, f w ≠ v) (e : Sym2 W) : degContrib pV v (edgeEmb f e) = 0 := by
  induction e using Sym2.ind with
  | _ a b =>
    funext i
    simp [edgeEmb, degContrib, hv]

/-- Structural (or any) integral divisibility moves along a vertex embedding which
preserves the labels. Vertices outside the image have zero degree vector. -/
theorem isIntDiv_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) {F : Finset (Multiset (Fin t))} {P : Finset (Sym2 W)}
    (h : IsIntDiv pW F P) : IsIntDiv pV F (P.map (edgeEmb f)) := by
  obtain ⟨⟨c, hc⟩, hdeg⟩ := h
  refine ⟨⟨c, ?_⟩, fun v => ?_⟩
  · rw [← hc, edgeVec, edgeVec, sum_map]
    exact sum_congr rfl fun e _ => pairVec_map f hp e
  · by_cases hv : ∃ w, f w = v
    · obtain ⟨w, rfl⟩ := hv
      obtain ⟨c', hc'⟩ := hdeg w
      refine ⟨c', ?_⟩
      rw [hp, ← hc', degVec, degVec, sum_map]
      exact sum_congr rfl fun e _ => degContrib_map f hp w e
    · simp only [not_exists] at hv
      refine ⟨0, ?_⟩
      rw [degVec, sum_map]
      simp [degContrib_map_outside f pV hv]

/-- Integral divisibility pulls back along a label-preserving embedding. -/
theorem isIntDiv_comap (f : W ↪ V) {pV : V → Fin t} {F : Finset (Multiset (Fin t))}
    {P : Finset (Sym2 W)} (h : IsIntDiv pV F (P.map (edgeEmb f))) : IsIntDiv (pV ∘ f) F P := by
  obtain ⟨⟨c, hc⟩, hdeg⟩ := h
  refine ⟨⟨c, ?_⟩, fun w => ?_⟩
  · rw [← hc, edgeVec, edgeVec, sum_map]
    exact sum_congr rfl fun e _ => (pairVec_map f (pW := pV ∘ f) (fun _ => rfl) e).symm
  · obtain ⟨c', hc'⟩ := hdeg (f w)
    refine ⟨c', ?_⟩
    have : degVec (pV ∘ f) P w = degVec pV (P.map (edgeEmb f)) (f w) := by
      rw [degVec, degVec, sum_map]
      exact sum_congr rfl fun e _ => (degContrib_map f (pW := pV ∘ f) (fun _ => rfl) w e).symm
    rw [this, hc']
    rfl

/-- Pull back a decomposition through an embedding. -/
theorem isDecomp_of_map (f : W ↪ V) {pV : V → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 W)} {D : Finset (Finset W)}
    (h : IsDecomp pV F (E.map (edgeEmb f)) (D.map (setEmb f))) :
    IsDecomp (pV ∘ f) F E D := by
  obtain ⟨hT, hP, hU⟩ := h
  refine ⟨fun s hs => ?_, fun s hs u hu hsu => ?_, ?_⟩
  · have h := hT (s.map f) (mem_map_of_mem (setEmb f) hs)
    refine ⟨by simpa using h.1, ?_⟩
    have h2 := h.2
    simpa [Multiset.map_map] using h2
  · have hne : s.map f ≠ u.map f := fun h => hsu (map_injective f h)
    have := hP (mem_map_of_mem (setEmb f) hs) (mem_map_of_mem (setEmb f) hu) hne
    simp only [Function.onFun, setEmb, Function.Embedding.coeFn_mk, triEdges_map] at this
    exact (disjoint_map _).mp this
  · apply map_injective (edgeEmb f)
    rw [← hU]
    ext e
    simp only [mem_biUnion, mem_map, setEmb, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨e', ⟨s', hs', he'⟩, rfl⟩
      refine ⟨s'.map f, ⟨s', hs', rfl⟩, ?_⟩
      rw [triEdges_map]
      exact mem_map_of_mem _ he'
    · rintro ⟨s, ⟨s', hs', rfl⟩, he⟩
      rw [triEdges_map] at he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      exact ⟨e', ⟨s', hs', he'⟩, rfl⟩

/-- **Support extraction.** A decomposition of an embedded edge set comes from a
decomposition of the source edge set, for the pulled-back labels. -/
theorem hasDecomp_comap [Finite W] (f : W ↪ V) {pV : V → Fin t}
    {F : Finset (Multiset (Fin t))} {E : Finset (Sym2 W)}
    (h : HasDecomp pV F (E.map (edgeEmb f))) : HasDecomp (pV ∘ f) F E := by
  classical
  have := Fintype.ofFinite W
  obtain ⟨D, hD⟩ := h
  have hrange : ∀ s ∈ D, ∀ a ∈ s, ∃ w, f w = a := by
    intro s hs a ha
    obtain ⟨b, -, hab⟩ := exists_edge_of_mem (hD.1 s hs) ha
    have hE : s(a, b) ∈ E.map (edgeEmb f) := hD.2.2 ▸ mem_biUnion.mpr ⟨s, hs, hab⟩
    obtain ⟨e, -, he⟩ := mem_map.mp hE
    have hae : a ∈ edgeEmb f e := he ▸ Sym2.mem_mk_left a b
    simp only [edgeEmb, Function.Embedding.coeFn_mk, Sym2.mem_map] at hae
    obtain ⟨w, -, hw⟩ := hae
    exact ⟨w, hw⟩
  let DW : Finset (Finset W) := univ.filter fun s => s.map f ∈ D
  have hDW : DW.map (setEmb f) = D := by
    ext s
    simp only [mem_map, DW, mem_filter, mem_univ, true_and, setEmb,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨s', hs', rfl⟩
      exact hs'
    · intro hs
      have hpre : (univ.filter fun w => f w ∈ s).map f = s := by
        ext a
        simp only [mem_map, mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact hw
        · intro ha
          obtain ⟨w, rfl⟩ := hrange s hs a ha
          exact ⟨w, ha, rfl⟩
      exact ⟨univ.filter fun w => f w ∈ s, by rw [hpre]; exact hs, hpre⟩
  refine ⟨DW, isDecomp_of_map f ?_⟩
  rw [hDW]
  exact hD

end Embedding

end PartitionedTriangleAbsorption.PrivateTemplateStage69
