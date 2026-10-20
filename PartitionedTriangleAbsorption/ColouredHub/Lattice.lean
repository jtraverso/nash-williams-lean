/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Main
public import PartitionedTriangleAbsorption.TypedBoundedCoefficients
public import PartitionedTriangleAbsorption.OrdinaryDecompositionTransport

/-! # Signed-lattice pieces of bounded size

Combine the coloured-hub producer with the accepted Stage35 padding results:

* `TypedBoundedCoefficients.bounded_padding_package` chooses, for fixed `F` and `K`, a bound
  `B` **before** the vertex type, the partition and the piece; for `|P| ≤ K` with an integral
  global coefficient vector it supplies decomposable fresh padding `Q` (at most `3B` edges,
  disjoint from `P`, meeting no original vertex) such that `P ∪ Q` has the nonnegative
  coefficients `max (c τ) 0`;
* padding preserves even degrees and looplessness (`padded_even`, `padded_loopless`);
* the producer gives an absorber `A'` of `P ∪ Q`; then `A' ∪ Q` absorbs `P`
  (`TypedLatticePadding.absorber_of_padding`).

Bounds: `|A| ≤ 105 (|P| + |Q|) + |Q| ≤ 105 K + 318 B`, at most `34 K + 105 B + t` new vertices,
and `d_A(v) = 4 d_P(v)` at original vertices. `B` is existential (no explicit growth rate),
and it bounds the coefficient witness *chosen* here, not an arbitrary supplied witness.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate TypedTransformer AntiEdgeSelection OnePart TypedLatticePadding
  TypedPaddingProducer TypedBoundedCoefficients

variable {t : ℕ}

/-! ### Transport and degree facts -/

section Transport

variable {W V : Type*} [DecidableEq W] [DecidableEq V]

/-- Typed decompositions transport along part-preserving injective vertex maps. -/
theorem hasDecomp_image_typed {q : W → Fin t} {q' : V → Fin t} {F : Finset (Multiset (Fin t))}
    (f : W → V) (hf : Function.Injective f) (hq : ∀ w, q' (f w) = q w)
    (E : Finset (Sym2 W)) (hE : HasDecomp q F E) :
    HasDecomp q' F (E.image (Sym2.map f)) := by
  obtain ⟨D, htri, hdis, hcover⟩ := hE
  refine ⟨D.image (fun s => s.image f), ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s, hpre, rfl⟩ := mem_image.mp hs
    refine ⟨(card_image_of_injective s hf).trans (htri s hpre).1, ?_⟩
    rw [image_val_of_injOn hf.injOn, Multiset.map_map]
    have : q' ∘ f = q := funext hq
    rw [this]
    exact (htri s hpre).2
  · intro s hs s' hs' hne
    obtain ⟨s, hpre, rfl⟩ := mem_image.mp hs
    obtain ⟨s', hpre', rfl⟩ := mem_image.mp hs'
    change Disjoint (triEdges (s.image f)) (triEdges (s'.image f))
    rw [OrdinaryDecompositionTransport.triEdges_image f hf,
      OrdinaryDecompositionTransport.triEdges_image f hf, disjoint_left]
    intro e he he'
    obtain ⟨a, ha, rfl⟩ := mem_image.mp he
    obtain ⟨b, hb, hab⟩ := mem_image.mp he'
    have hab' : b = a := Sym2.map.injective hf hab
    subst b
    exact disjoint_left.mp (hdis hpre hpre' (fun h => hne (h ▸ rfl))) ha hb
  · rw [image_biUnion]
    simp_rw [OrdinaryDecompositionTransport.triEdges_image f hf]
    rw [← biUnion_image, hcover]

/-- Degrees are preserved by an injective vertex map. -/
theorem incidentLoad_image_apply (f : W → V) (hf : Function.Injective f) (E : Finset (Sym2 W))
    (w : W) : incidentLoad (E.image (Sym2.map f)) (f w) = incidentLoad E w := by
  unfold incidentLoad
  rw [filter_image, card_image_of_injective _ (Sym2.map.injective hf)]
  congr 1
  ext e
  simp [Sym2.mem_map, hf.eq_iff]

omit [DecidableEq W] in
/-- Vertices outside the image have degree zero in the image. -/
theorem incidentLoad_image_of_notMem (f : W → V) (E : Finset (Sym2 W)) (v : V)
    (hv : ∀ w, f w ≠ v) : incidentLoad (E.image (Sym2.map f)) v = 0 := by
  unfold incidentLoad
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hve
  obtain ⟨e', -, rfl⟩ := mem_image.mp he
  obtain ⟨w, -, rfl⟩ := Sym2.mem_map.mp hve
  exact hv w rfl

omit [DecidableEq V] in
/-- A decomposable edge set has even degrees. -/
theorem even_incidentLoad_of_hasDecomp {q : W → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 W)} (hE : HasDecomp q F E) (v : W) : Even (incidentLoad E v) := by
  obtain ⟨D, htri, hdis, rfl⟩ := hE
  refine even_incidentLoad_biUnion D triEdges hdis (fun s hs u => ?_) v
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp (htri s hs).1
  rw [triEdges_three hab hac hbc]
  have e : ({s(a, b), s(a, c), s(b, c)} : Finset (Sym2 W)) = {s(a, b), s(b, c), s(c, a)} := by
    ext x; simp only [mem_insert, mem_singleton, Sym2.eq_swap (a := a) (b := c)]; tauto
  rw [e]
  exact PrivateTemplate.even_incidentLoad_tri hab hac hbc u

omit [DecidableEq V] in
/-- A decomposable edge set is loopless. -/
theorem loopless_of_hasDecomp {q : W → Fin t} {F : Finset (Multiset (Fin t))}
    {E : Finset (Sym2 W)} (hE : HasDecomp q F E) : ∀ e ∈ E, ¬ e.IsDiag := by
  obtain ⟨D, -, -, rfl⟩ := hE
  intro e he
  obtain ⟨s, -, hs⟩ := mem_biUnion.mp he
  exact (mem_filter.mp hs).2

end Transport

/-! ### Padding preserves the hypotheses of the producer -/

section Padding

variable {W T : Type*} [DecidableEq W] [Fintype T] [DecidableEq T]

/-- **Padding preserves even degrees.** -/
theorem padded_even {q : Ext W T → Fin t} {F : Finset (Multiset (Fin t))}
    (P : Finset (Sym2 W)) (heven : ∀ v, Even (incidentLoad P v))
    (hQ : HasDecomp q F (padding (W := W) (T := T))) (v : Ext W T) :
    Even (incidentLoad (liftE (T := T) P ∪ padding (W := W) (T := T)) v) := by
  refine even_incidentLoad_union (padding_disjoint_lift P) (fun u => ?_)
    (even_incidentLoad_of_hasDecomp hQ) v
  rcases u with w | x
  · rw [liftE, incidentLoad_image_apply Sum.inl Sum.inl_injective]; exact heven w
  · rw [liftE, incidentLoad_image_of_notMem Sum.inl P _ (fun _ => Sum.inl_ne_inr)]
    exact ⟨0, rfl⟩

/-- **Padding preserves looplessness.** -/
theorem padded_loopless {q : Ext W T → Fin t} {F : Finset (Multiset (Fin t))}
    (P : Finset (Sym2 W)) (hloop : ∀ e ∈ P, ¬ e.IsDiag)
    (hQ : HasDecomp q F (padding (W := W) (T := T))) :
    ∀ e ∈ liftE (T := T) P ∪ padding (W := W) (T := T), ¬ e.IsDiag := by
  intro e he
  rcases mem_union.mp he with he | he
  · obtain ⟨e', he', rfl⟩ := mem_image.mp he
    rw [Sym2.isDiag_map Sum.inl_injective]
    exact hloop e' he'
  · exact loopless_of_hasDecomp hQ e he

end Padding

/-! ### The bounded signed-lattice corollary -/

/-- **Bounded signed-lattice pieces have coloured-hub absorbers.** For fixed `F` (size-three
types, `ThreeStepLinks`) and `K`, there is `B`, chosen before the vertex type, partition and
piece, such that every loopless even piece `P` with `|P| ≤ K` and an *integral* global
coefficient vector has an absorber `A` on the explicit vertex type
`(W ⊕ (Index F c × Fin 3)) ⊕ HAux m' t`, with original vertices `Sum.inl (Sum.inl w)`:
no edge of `A` joins two original vertices, `A` and `A ∪ P` decompose exactly,
`|A| ≤ 105 K + 318 B`, at most `34 K + 105 B + t` new vertices, and `d_A(v) = 4 d_P(v)`. -/
theorem bounded_lattice_absorber (F : Finset (Multiset (Fin t)))
    (hF3 : ∀ τ ∈ F, Multiset.card τ = 3) (hF : ThreeStepLinks F) (K : ℕ) :
    ∃ B : ℕ, ∀ {W : Type} [DecidableEq W] (p : W → Fin t) (P : Finset (Sym2 W)),
      P.card ≤ K → (∀ e ∈ P, ¬ e.IsDiag) → (∀ v, Even (incidentLoad P v)) →
      (∃ c : Multiset (Fin t) → ℤ, edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ) →
      ∃ (c : Multiset (Fin t) → ℤ) (m' : ℕ) (p' : HV (Ext W (Index F c)) m' t → Fin t)
        (A : Finset (Sym2 (HV (Ext W (Index F c)) m' t))),
        (∀ v, p' (Sum.inl (Sum.inl v)) = p v) ∧
        (∀ u v : W, s(Sum.inl (Sum.inl u), Sum.inl (Sum.inl v)) ∉ A) ∧
        Disjoint A (liftOld m' (liftE (T := Index F c) P)) ∧
        HasDecomp p' F A ∧
        HasDecomp p' F (A ∪ liftOld m' (liftE (T := Index F c) P)) ∧
        A.card ≤ 105 * K + 318 * B ∧
        Fintype.card (Index F c × Fin 3) + Fintype.card (HAux m' t) ≤ 34 * K + 105 * B + t ∧
        (∀ v, incidentLoad A (Sum.inl (Sum.inl v)) = 4 * incidentLoad P v) := by
  obtain ⟨B, hB⟩ := bounded_padding_package F hF3 K
  refine ⟨B, fun {W} _ p P hK hloop heven hc => ?_⟩
  obtain ⟨c, hdisj, hQdec, hQcard, hQold, hvec⟩ := hB p P hK hc
  set σ := labels F hF3 c
  set Q := padding (W := W) (T := Index F c) with hQdef
  set P' := liftE (T := Index F c) P ∪ Q with hP'def
  have hvec' : edgeVec (extPart p σ) P' =
      ∑ τ ∈ F, (((c τ).toNat : ℕ) : ℤ) • typeEdgeVec τ := by
    rw [hvec]
    refine sum_congr rfl fun τ _ => ?_
    rw [Int.toNat_eq_max]
  obtain ⟨p', A', hp', -, hnoold, hdis', hA', hA'P, hcardA', hcardAux, hdeg', -⟩ :=
    exists_colouredHubAbsorber (extPart p σ) F hF3 hF P' (padded_loopless P hloop hQdec)
      (padded_even P heven hQdec) (fun τ => (c τ).toNat) hvec'
  have hliftU : liftOld (t := t) P'.card P' =
      liftOld P'.card (liftE (T := Index F c) P) ∪ liftOld P'.card Q := by
    simp only [liftOld, hP'def, image_union]
  have hQlift : HasDecomp p' F (liftOld (t := t) P'.card Q) :=
    hasDecomp_image_typed Sum.inl Sum.inl_injective hp' Q hQdec
  have hPQ : Disjoint (liftOld (t := t) P'.card (liftE (T := Index F c) P)) (liftOld P'.card Q) :=
    (disjoint_image (Sym2.map.injective Sum.inl_injective)).mpr hdisj
  have hdisU : Disjoint A' (liftOld P'.card (liftE (T := Index F c) P) ∪ liftOld P'.card Q) :=
    hliftU ▸ hdis'
  have hA'PU : HasDecomp p' F
      (A' ∪ (liftOld P'.card (liftE (T := Index F c) P) ∪ liftOld P'.card Q)) :=
    hliftU ▸ hA'P
  obtain ⟨hfin1, hfin2, hfin3⟩ := absorber_of_padding hPQ hQlift hdisU hA' hA'PU
  have hQeq : Q.card = 3 * Fintype.card (Index F c) := padding_card
  have hm' : P'.card = P.card + Q.card := by
    rw [hP'def, card_union_of_disjoint (padding_disjoint_lift P), liftE,
      card_image_of_injective _ (Sym2.map.injective Sum.inl_injective)]
  have hQold' : ∀ u : W, ∀ e ∈ Q, (Sum.inl u : Ext W (Index F c)) ∉ e := by
    intro u e he hu
    have h0 := hQold u
    unfold incidentLoad at h0
    rw [card_eq_zero, filter_eq_empty_iff] at h0
    exact h0 he hu
  refine ⟨c, P'.card, p', A' ∪ liftOld P'.card Q, fun v => hp' (Sum.inl v), ?_, hfin1, hfin2, hfin3,
    ?_, ?_, fun v => ?_⟩
  · intro u v h
    rcases mem_union.mp h with h | h
    · exact hnoold _ _ h
    · obtain ⟨e, he, hee⟩ := mem_image.mp h
      have : e = s(Sum.inl u, Sum.inl v) :=
        Sym2.map.injective Sum.inl_injective (by simpa using hee)
      subst this
      exact hQold' u _ he (Sym2.mem_mk_left _ _)
  · have hQc : Q.card ≤ 3 * B := hQcard
    have h1 := card_union_le A' (liftOld (t := t) P'.card Q)
    have h2 : (liftOld (t := t) P'.card Q).card ≤ Q.card := card_image_le
    omega
  · have hQc : Q.card ≤ 3 * B := hQcard
    rw [Fintype.card_prod, Fintype.card_fin, card_hAux]
    omega
  · have hd : Disjoint A' (liftOld (t := t) P'.card Q) := hdisU.mono_right subset_union_right
    rw [incidentLoad_union hd, hdeg', liftOld,
      incidentLoad_image_apply Sum.inl Sum.inl_injective, hP'def,
      incidentLoad_union (padding_disjoint_lift P), liftE,
      incidentLoad_image_apply Sum.inl Sum.inl_injective, hQold v]
    ring

end PartitionedTriangleAbsorption.ColouredHub
