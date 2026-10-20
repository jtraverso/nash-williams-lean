/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0FlexibleCompressed

/-! # The compatible-label compressed F0 producer with its library exposed

`F0FlexibleCompressed.flexible_producer` (Stage43) hides its piece function. For a physical
shared realization we need the actual pieces. This module re-runs the same proof (unchanged
mathematics) with two extra visible facts:

* the piece function is the concrete `flexB p label X hX = (evenRef p X hX).Bt label`, where
  `evenRef p X hX` is exactly the parity refiner used inside `flexible_producer`; the charge
  correction is rebuilt for `label` (it is *not* a relabelling of an older corrected library);
* every parity index `Sum.inl i` of the library has `i` in the even library.

`compatB p pV X hX` is the instance at the Stage43 compatible labels `compatibleMid p pV`.
No accepted source is changed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks

variable {W0 : Type*} [DecidableEq W0] {κ : Type*} [DecidableEq κ]

namespace EvenRefiner

variable {X0 : Finset (Sym2 W0)} (pw0 : W0 → Fin 2) (E : EvenRefiner κ X0)

/-- `charge_layer`, additionally exposing that parity indices come from `E.lib`. -/
theorem charge_layer_exposed : ∃ (indices : Finset (JIdx κ)) (R : Finset (Sym2 (W1 W0 κ))),
    Disjoint R (liftE X0) ∧
    RefinerAssembly.RefinesReserve (p := pw1 pw0) (F := F0) indices (E.Bt pw0) (liftE X0) R ∧
    (∀ j ∈ indices, IsIntDiv (pw1 pw0) F0 (E.Bt pw0 j) ∧ (∀ e ∈ E.Bt pw0 j, ¬ e.IsDiag) ∧
      E.Bt pw0 j ⊆ R ∪ liftE X0 ∧ (E.Bt pw0 j).card ≤ 9 * (E.oldPart j).card + 16) ∧
    (∀ w, ∑ j ∈ indices, incidentLoad (E.Bt pw0 j) (Sum.inl w) =
      ∑ i ∈ E.lib, incidentLoad (E.P i) w) ∧
    (∀ t a, ∑ j ∈ indices, incidentLoad (E.Bt pw0 j) (Sum.inr (t, a)) ≤ 88) ∧
    indices.card ≤ E.lib.card + 97 * ∑ i ∈ E.lib, (E.P i).card ∧
    (∀ i, (Sum.inl i : JIdx κ) ∈ indices → i ∈ E.lib) := by
  -- the parity selection of the empty leftover bounds the number of present slots
  obtain ⟨T0, hT0, hdis0, hU0⟩ := E.refines ∅ (empty_subset _) (fun w => by
    simp [incidentLoad])
  have hs : E.sNum pw0 ≤ E.z pw0 := by
    rw [← E.card_Zs_eq pw0 hT0 hdis0 (empty_subset _) (charge_empty _ _) hU0, card_Zs pw0 E hT0]
    exact card_le_card (E.Zd_subset pw0 hT0)
  -- the robust graph is fixed before any leftover
  obtain ⟨m, H, hm, hHfst, hHsnd, hdx, hdy, hmatch⟩ := exists_robust (E.z pw0) (E.sNum pw0) hs
  refine ⟨E.indices pw0 H, E.Rt pw0 m, ?_, ?_, ?_, fun w => E.sum_inl_load pw0 w,
    fun t a => E.sum_inr_load pw0 hdx hdy t a, ?_, fun i hi => by simpa [indices] using hi⟩
  · rw [← piece_empty_ids]
    exact disjoint_piece E.disjRX (disjoint_empty_right _)
  · intro L hL hdiv
    obtain ⟨L0, hL0, rfl⟩ := exists_liftE_of_subset hL
    have hloopL : ∀ e ∈ liftE (κ := κ) L0, ¬ e.IsDiag :=
      loopless_mapE Sum.inl_injective (fun e he => E.loopX e (hL0 he))
    have hevenL0 : ∀ w, Even (incidentLoad L0 w) := by
      intro w
      have := TypedDivisibilityCollapse.even_of_isIntDiv TypedTransportExamples.F0_card hloopL
        hdiv (Sum.inl w)
      rwa [liftE, incidentLoad_mapE_apply Sum.inl_injective] at this
    have hqL0 : charge chi0 pw0 L0 = 0 := by
      have := charge_eq_zero_of_isIntDiv kills_chi0 hdiv
      rwa [liftE, charge_mapE _ Sum.inl_injective] at this
    obtain ⟨T, hT, hdisT, hU⟩ := E.refines L0 hL0 hevenL0
    have hcard := E.card_Zs_eq pw0 hT hdisT hL0 hqL0 hU
    obtain ⟨f, hinj, hedge, himg⟩ := hmatch (E.Zs pw0 T) (E.Zs_subset pw0 hT) hcard
    refine ⟨E.sel pw0 T (m + E.sNum pw0) f, ?_, ?_, ?_⟩
    · intro j hj
      simp only [sel, mem_union, mem_image, Function.comp_apply] at hj
      simp only [indices, mem_union, mem_image, Function.comp_apply]
      rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨x, hx, rfl⟩
      · exact Or.inl (Or.inl ⟨i, hT hi, rfl⟩)
      · obtain ⟨hi, -, hk⟩ := (E.mem_relSel pw0).mp hr
        exact Or.inl (Or.inr ⟨r, (E.mem_relIdx pw0).mpr ⟨hi, hk⟩, rfl⟩)
      · exact Or.inr ⟨(x, f x), hedge x (mem_range.mp hx), rfl⟩
    · intro j hj j' hj' hne
      exact disjoint_piece (E.pairwiseDisjoint_oldPart pw0 hdisT hj hj' hne)
        (E.pairwiseDisjoint_ids pw0 hT hinj himg hj hj' hne)
    · unfold Bt
      rw [biUnion_piece, E.biUnion_oldPart_sel pw0, E.biUnion_ids_sel pw0 hT himg, hU, Rt]
      rw [← piece_empty_ids L0, piece_union, union_empty]
  · intro j hj
    have hsub : E.Bt pw0 j ⊆ E.Rt pw0 m ∪ liftE X0 := by
      unfold Bt Rt
      have : E.Rt pw0 m ∪ liftE X0 = piece (E.R0 ∪ X0) (E.allIds pw0 m) := by
        rw [Rt, ← piece_empty_ids X0, piece_union, union_empty]
      rw [← Rt, this]
      exact piece_mono (E.oldPart_subset pw0 hj) (E.ids_subset_allIds pw0 hHfst hHsnd hj)
    have hloop : ∀ e ∈ E.oldPart j, ¬ e.IsDiag := by
      rcases j with i | j
      · have hi : i ∈ E.lib := by simpa [indices] using hj
        exact E.loopP i hi
      · simp [oldPart]
    have heven : ∀ w, Even (incidentLoad (E.oldPart j) w) := by
      rcases j with i | j
      · have hi : i ∈ E.lib := by simpa [indices] using hj
        exact E.evenP i hi
      · intro w; simp [oldPart, incidentLoad]
    refine ⟨isIntDiv_piece pw0 hloop heven _ ?_, loopless_piece hloop _, hsub, ?_⟩
    · simp only [indices, mem_union, mem_image, Function.comp_apply] at hj
      rcases hj with (⟨i, hi, rfl⟩ | ⟨r, -, rfl⟩) | ⟨h, -, rfl⟩
      · exact E.charge_par_zero pw0 hi
      · exact E.charge_rel_zero pw0 r
      · exact charge_mt_zero pw0 h
    · refine (card_piece_le _ _).trans ?_
      simp only [indices, mem_union, mem_image, Function.comp_apply] at hj
      rcases hj with (⟨i, hi, rfl⟩ | ⟨r, -, rfl⟩) | ⟨h, -, rfl⟩
      · have h1 : (E.ids pw0 (Sum.inl i)).card ≤ E.mc pw0 i + E.pc pw0 i := by
          simp only [ids, idsPar]
          refine (card_union_le _ _).trans (Nat.add_le_add ?_ ?_) <;>
            exact card_image_le.trans (by simp)
        have h2 := E.mc_add_pc_le pw0 i
        simp only [oldPart] at h1 ⊢
        omega
      · have : (E.ids pw0 (Sum.inr (Sum.inl r))).card ≤ 2 := card_le_two
        simp only [oldPart, card_empty] at this ⊢
        omega
      · have : (E.ids pw0 (Sum.inr (Sum.inr h))).card ≤ 2 := card_le_two
        simp only [oldPart, card_empty] at this ⊢
        omega
  · have hH := card_le_of_fst hHfst hdx
    have hz := E.z_le pw0
    have hrel : (E.relIdx pw0).card ≤ E.z pw0 := by
      rw [card_relIdx, z_eq]; exact sum_le_sum fun i _ => Nat.le_add_left _ _
    unfold indices
    refine (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
      (Nat.add_le_add card_image_le card_image_le)) card_image_le) |>.trans ?_
    nlinarith


end EvenRefiner

namespace CompressedHub.CompatibleShared

open UniversalRefiner F0FlexibleCompressed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The even (parity) refiner underlying the compressed F0 producer; it is the refiner `E`
inside `F0FlexibleCompressed.flexible_producer`, and does not depend on labels. -/
noncomputable def evenRef (p : ℕ) (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    EvenRefiner (W0 := WP (RefU V p)) (LibIdx (RefU V p)) (mapE Sum.inl (mapE Sum.inl X)) :=
  parityRefiner (X := mapE Sum.inl X) (hmap := heapH p) (L := p + 1) (hubOf p 0)
    (loopless_mapE Sum.inl_injective hX) (heap_links_last X) (heap_nofix X)

/-- The reserve lifted to `RefU V p` (an abbreviation). -/
abbrev cX1 (p : ℕ) (X : Finset (Sym2 V)) : Finset (Sym2 (RefU V p)) := mapE Sum.inl X

/-- The concrete piece function of the flexible producer, charge correction rebuilt for
`label`. -/
noncomputable def flexB (p : ℕ) (label : WP (RefU V p) → Fin 2) (X : Finset (Sym2 V))
    (hX : ∀ e ∈ X, ¬ e.IsDiag) : RefI V p → Finset (Sym2 (RefW V p)) :=
  (evenRef p X hX).Bt label

/-- The concrete piece function of the Stage43 compatible producer. -/
noncomputable abbrev compatB (p : ℕ) (pV : V → Fin 2) (X : Finset (Sym2 V))
    (hX : ∀ e ∈ X, ¬ e.IsDiag) : RefI V p → Finset (Sym2 (RefW V p)) :=
  flexB p (compatibleMid p pV) X hX

/-- **`flexible_producer` with the concrete library exposed.** Same conclusions and bounds as
`F0FlexibleCompressed.flexible_producer`, for the concrete piece function `flexB`, plus the
fact that every parity index of the library lies in the even library. -/
theorem flexible_producer_exposed (p : ℕ) (label : WP (RefU V p) → Fin 2)
    (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∃ (indices : Finset (RefI V p)) (R : Finset (Sym2 (RefW V p))),
      Disjoint R (mapE (refEmb p) X) ∧
      RefinerAssembly.RefinesReserve (p := pw1 label) (F := F0)
        indices (flexB p label X hX) (mapE (refEmb p) X) R ∧
      (∀ j ∈ indices, IsIntDiv (pw1 label) F0 (flexB p label X hX j) ∧
        (∀ e ∈ flexB p label X hX j, ¬ e.IsDiag) ∧
        (∀ w, Even (incidentLoad (flexB p label X hX j) w)) ∧
        flexB p label X hX j ⊆ R ∪ mapE (refEmb p) X ∧ (flexB p label X hX j).card ≤ 214) ∧
      (∀ v, ∑ j ∈ indices, incidentLoad (flexB p label X hX j) (refEmb p v) ≤
        99 * incidentLoad X v) ∧
      (∀ r, ∑ j ∈ indices, incidentLoad (flexB p label X hX j) (Sum.inl (Sum.inr r)) ≤ 66) ∧
      (∀ t a, ∑ j ∈ indices, incidentLoad (flexB p label X hX j) (Sum.inr (t,a)) ≤ 88) ∧
      (∀ D, (∀ v, incidentLoad X v ≤ D) → ∀ i : Fin (2 ^ (p + 1)),
        ∑ j ∈ indices, incidentLoad (flexB p label X hX j) (Sum.inl (Sum.inl (Sum.inr i))) ≤
          330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p) ∧
      indices.card ≤ 57635 * (X.card + 2 * (2 ^ p) ^ 2) ∧
      (∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib) := by
  unfold flexB
  obtain ⟨indices, R, hdisj, href, hpieces, hold, htok, hcard, hlibE⟩ :=
    (evenRef p X hX).charge_layer_exposed label
  have hlift : (liftE (κ := LibIdx (RefU V p)) (mapE Sum.inl (cX1 p X)) :
      Finset (Sym2 (RefW V p))) = mapE (refEmb p) X := by
    simp only [liftE, mapE_mapE]; rfl
  rw [hlift] at hdisj href hpieces
  have hPcard : ∀ i, ((evenRef p X hX).P i).card ≤ 22 := fun i =>
    (card_physE_le _ _).trans (by have := card_piece_le' (mapE Sum.inl X) (heapH p) i; omega)
  refine ⟨indices, R, hdisj, href, ?_, ?_, ?_, htok, ?_, ?_, hlibE⟩
  · intro j hj
    obtain ⟨hdiv, hloop, hsub, hc⟩ := hpieces j hj
    refine ⟨hdiv, hloop, fun w => TypedDivisibilityCollapse.even_of_isIntDiv
      TypedTransportExamples.F0_card hloop hdiv w, hsub, hc.trans ?_⟩
    have : ((evenRef p X hX).oldPart j).card ≤ 22 := by
      rcases j with i | j
      · exact hPcard i
      · simp [EvenRefiner.oldPart]
    omega
  · intro v
    rw [show (refEmb p v : RefW V p) = Sum.inl (Sum.inl (Sum.inl v)) from rfl, hold]
    refine (sum_evenLib_load_inl (cX1 p X) (heapH p) (p + 1) (hubOf p 0) (Sum.inl v)).trans ?_
    rw [heap_root_old X v]
    have h1 : (vChain (cX1 p X) (Sum.inl v)).card = incidentLoad X v :=
      incidentLoad_mapE_apply Sum.inl_injective X v
    rw [h1]
    omega
  · intro r
    rw [hold]
    exact sum_evenLib_load_inr (cX1 p X) (heapH p) (p + 1) (hubOf p 0) r
  · intro D hD i
    rw [hold]
    refine (sum_evenLib_load_inl (cX1 p X) (heapH p) (p + 1) (hubOf p 0) (Sum.inr i)).trans ?_
    have h1 : ∑ l ∈ range (p + 1), (2 * (vChain (links (cX1 p X) (heapH p) l) (Sum.inr i)).card +
        10 * hubWeight (links (cX1 p X) (heapH p) l) (heapH p l) (Sum.inr i)) ≤
        10 * ((Fintype.card V / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) :=
      heap_root_hub X D hD i
    have h2 : (vChain (cX1 p X) (Sum.inr i)).card = 0 := by
      rw [vChain_level0_hub]; rfl
    rw [h2]
    change _ ≤ 330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p
    have hp2 := pow_succ 2 p
    omega
  · refine hcard.trans ?_
    have hlib := card_evenLib_le (cX1 p X) (heapH p) (p + 1) (hubOf p 0)
    have hsum := sum_card_physE_le (cX1 p X) (heapH p) (p + 1) (hubOf p 0)
    have hL := heap_sum_links_compressed (p := p) X
    have hX1c : (cX1 p X).card = X.card := card_mapE Sum.inl_injective X
    change (evenLib (cX1 p X) (heapH p) (p + 1) (hubOf p 0)).card + 97 *
      ∑ i ∈ evenLib (cX1 p X) (heapH p) (p + 1) (hubOf p 0),
        (physE (rtP (heapH p) (hubOf p 0)) (UniversalRefiner.piece (cX1 p X) (heapH p) i)).card ≤ _
    rw [hX1c] at hsum
    nlinarith

/-- **The Stage43 compatible producer with its concrete library exposed** (instance of
`flexible_producer_exposed` at `compatibleMid p pV`, whose part function is
`compatiblePart p pV`). -/
theorem compatible_producer_exposed (p : ℕ) (pV : V → Fin 2)
    (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∃ (indices : Finset (RefI V p)) (R : Finset (Sym2 (RefW V p))),
      Disjoint R (mapE (refEmb p) X) ∧
      RefinerAssembly.RefinesReserve (p := compatiblePart p pV) (F := F0)
        indices (compatB p pV X hX) (mapE (refEmb p) X) R ∧
      (∀ j ∈ indices, IsIntDiv (compatiblePart p pV) F0 (compatB p pV X hX j) ∧
        (∀ e ∈ compatB p pV X hX j, ¬ e.IsDiag) ∧
        (∀ w, Even (incidentLoad (compatB p pV X hX j) w)) ∧
        compatB p pV X hX j ⊆ R ∪ mapE (refEmb p) X ∧ (compatB p pV X hX j).card ≤ 214) ∧
      (∀ v, ∑ j ∈ indices, incidentLoad (compatB p pV X hX j) (refEmb p v) ≤
        99 * incidentLoad X v) ∧
      (∀ r, ∑ j ∈ indices, incidentLoad (compatB p pV X hX j) (Sum.inl (Sum.inr r)) ≤ 66) ∧
      (∀ t a, ∑ j ∈ indices, incidentLoad (compatB p pV X hX j) (Sum.inr (t,a)) ≤ 88) ∧
      (∀ D, (∀ v, incidentLoad X v ≤ D) → ∀ i : Fin (2 ^ (p + 1)),
        ∑ j ∈ indices, incidentLoad (compatB p pV X hX j) (Sum.inl (Sum.inl (Sum.inr i))) ≤
          330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p) ∧
      indices.card ≤ 57635 * (X.card + 2 * (2 ^ p) ^ 2) ∧
      (∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib) :=
  flexible_producer_exposed p (compatibleMid p pV) X hX

end CompressedHub.CompatibleShared

end PartitionedTriangleAbsorption.TypedRefinerF0
