/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeLayerSelect

/-! # The charge layer: from an even refiner to a typed F0 refiner

`EvenRefiner.charge_layer`: every even refiner of a loopless reserve `X0` on `W0` (with an
arbitrary part function `pw0`) yields, on `W0 ⊕ (Tok κ × Fin 8)`, a fixed remainder `R` and a
fixed library of integrally F0-divisible pieces that refines **every** integrally
F0-divisible leftover `L ⊆ X0` (`RefinerAssembly.RefinesReserve`).

Quantifier order: the robust graph `H`, the remainder and the library are fixed first; only
then is the leftover chosen. The old-vertex incidence of the whole library equals that of
the even refiner, every token vertex lies in boundedly many pieces, pieces grow by a factor
at most `9`, and the library size grows linearly.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks

variable {W0 : Type*} [DecidableEq W0] {κ : Type*} [DecidableEq κ]

namespace EvenRefiner

variable {X0 : Finset (Sym2 W0)} (pw0 : W0 → Fin 2) (E : EvenRefiner κ X0)

theorem card_Zd (T : Finset κ) :
    (E.Zd pw0 T).card = ∑ i ∈ E.lib \ T, E.mc pw0 i + ∑ i ∈ T, E.pc pw0 i := by
  unfold Zd
  rw [card_union_of_disjoint]
  · rw [card_biUnion, card_biUnion]
    · congr 1
      · exact sum_congr rfl fun i _ => by
          rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
      · exact sum_congr rfl fun i _ => by
          rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
    · intro i _ i' _ hii'
      rw [Function.onFun, disjoint_left]
      intro d h1 h2
      obtain ⟨k, -, rfl⟩ := mem_image.mp h1
      obtain ⟨k', -, h⟩ := mem_image.mp h2
      simp only [Prod.mk.injEq] at h
      exact hii' h.1.symm
    · intro i _ i' _ hii'
      rw [Function.onFun, disjoint_left]
      intro d h1 h2
      obtain ⟨k, -, rfl⟩ := mem_image.mp h1
      obtain ⟨k', -, h⟩ := mem_image.mp h2
      simp only [Prod.mk.injEq] at h
      exact hii' h.1.symm
  · rw [disjoint_left]
    intro d h1 h2
    simp only [mem_biUnion, mem_image] at h1 h2
    obtain ⟨i, -, k, -, rfl⟩ := h1
    obtain ⟨i', -, k', -, h⟩ := h2
    simp at h

theorem card_Zs {T : Finset κ} (hT : T ⊆ E.lib) : (E.Zs pw0 T).card = (E.Zd pw0 T).card :=
  card_image_of_injOn fun _ hd _ hd' h =>
    E.slot_inj pw0 (E.Zd_subset pw0 hT hd) (E.Zd_subset pw0 hT hd') h

/-- **Charge conservation fixes the number of present variable slots.** -/
theorem card_Zs_eq {T : Finset κ} (hT : T ⊆ E.lib) (hdisT : (T : Set κ).PairwiseDisjoint E.P)
    {L0 : Finset (Sym2 W0)} (hL0 : L0 ⊆ X0) (hq : charge chi0 pw0 L0 = 0)
    (hU : T.biUnion E.P = E.R0 ∪ L0) : (E.Zs pw0 T).card = E.sNum pw0 := by
  have hR : charge chi0 pw0 E.R0 = 4 * ∑ i ∈ T, E.chg pw0 i := by
    have h1 : charge chi0 pw0 (T.biUnion E.P) = ∑ i ∈ T, charge chi0 pw0 (E.P i) :=
      charge_biUnion _ _ _ _ hdisT
    have hdis : Disjoint E.R0 L0 := disjoint_of_subset_right hL0 E.disjRX
    rw [hU, charge_union _ _ hdis, hq, add_zero] at h1
    rw [h1, mul_sum]
    exact sum_congr rfl fun i hi => E.charge_eq_four_chg pw0 (hT hi)
  have hc0 : charge chi0 pw0 E.R0 / 4 = ∑ i ∈ T, E.chg pw0 i := by
    rw [hR]; exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [card_Zs pw0 E hT, card_Zd pw0 E T, sNum, hc0]
  have hsplit : ∑ i ∈ E.lib, (E.mc pw0 i : ℤ) =
      ∑ i ∈ E.lib \ T, (E.mc pw0 i : ℤ) + ∑ i ∈ T, (E.mc pw0 i : ℤ) :=
    (sum_sdiff hT).symm
  have hchg : ∑ i ∈ T, E.chg pw0 i = ∑ i ∈ T, ((E.mc pw0 i : ℤ) - E.pc pw0 i) :=
    sum_congr rfl fun i _ => E.chg_eq pw0 i
  rw [hsplit, hchg, sum_sub_distrib]
  have : ∑ i ∈ E.lib \ T, (E.mc pw0 i : ℤ) + ∑ i ∈ T, (E.mc pw0 i : ℤ) -
      (∑ i ∈ T, (E.mc pw0 i : ℤ) - ∑ i ∈ T, (E.pc pw0 i : ℤ)) =
      ((∑ i ∈ E.lib \ T, E.mc pw0 i + ∑ i ∈ T, E.pc pw0 i : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]

/-! ### Membership in the library -/

theorem ids_subset_allIds {m : ℕ} {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hHfst : ∀ h ∈ H, h.1 < m + E.sNum pw0)
    (hHsnd : ∀ h ∈ H, h.2 ∈ (range m).disjSum (range (E.z pw0)))
    {j : JIdx κ} (hj : j ∈ E.indices pw0 H) : E.ids pw0 j ⊆ E.allIds pw0 m := by
  intro t ht
  simp only [indices, mem_union, mem_image, Function.comp_apply] at hj
  simp only [allIds, mem_union, mem_image, mem_range]
  rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨h, hh, rfl⟩
  · simp only [ids, idsPar, mem_union, mem_image, mem_range] at ht
    rcases ht with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact Or.inl (Or.inl (Or.inr ⟨_, E.slot_lt pw0 (E.mem_D_false pw0 hi hk), rfl⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨(i, k), (E.mem_relIdx pw0).mpr ⟨hi, hk⟩, rfl⟩))
  · obtain ⟨hi, hk⟩ := (E.mem_relIdx pw0).mp hr
    simp only [ids, idsRel, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, E.slot_lt pw0 (E.mem_D_true pw0 hi hk), rfl⟩))
  · simp only [ids, idsMt, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (Or.inr ⟨h.1, hHfst h hh, rfl⟩)
    · have := hHsnd h hh
      rcases hh2 : h.2 with y | j'
      · rw [hh2] at this
        have : y < m := by simpa using this
        exact Or.inr ⟨y, this, by simp [minusId]⟩
      · rw [hh2] at this
        have : j' < E.z pw0 := by simpa using this
        exact Or.inl (Or.inl (Or.inr ⟨j', this, by simp [minusId]⟩))

theorem oldPart_subset {H : Finset (ℕ × (ℕ ⊕ ℕ))} {j : JIdx κ} (hj : j ∈ E.indices pw0 H) :
    E.oldPart j ⊆ E.R0 ∪ X0 := by
  rcases j with i | j
  · have hi : i ∈ E.lib := by simpa [indices] using hj
    exact E.subP i hi
  · exact empty_subset _

theorem piece_empty_ids (A : Finset (Sym2 W0)) : piece A (∅ : Finset (Tok κ)) = liftE A := by
  unfold piece tokU; simp

theorem piece_mono {A A' : Finset (Sym2 W0)} {S S' : Finset (Tok κ)} (hA : A ⊆ A')
    (hS : S ⊆ S') : piece A S ⊆ piece A' S' := by
  unfold piece liftE tokU mapE
  exact union_subset_union (image_subset_image hA) (biUnion_subset_biUnion_of_subset_left _ hS)

/-! ### Loads -/

theorem sum_inl_load {H : Finset (ℕ × (ℕ ⊕ ℕ))} (w : W0) :
    ∑ j ∈ E.indices pw0 H, incidentLoad (E.Bt pw0 j) (Sum.inl w) =
      ∑ i ∈ E.lib, incidentLoad (E.P i) w := by
  simp only [Bt, incidentLoad_piece_inl]
  unfold indices
  rw [union_assoc]
  have hrest : ∑ j ∈ (E.relIdx pw0).image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr),
      incidentLoad (E.oldPart j) w = 0 := by
    refine sum_eq_zero fun j hj => ?_
    simp only [mem_union, mem_image, Function.comp_apply] at hj
    rcases hj with ⟨r, -, rfl⟩ | ⟨h, -, rfl⟩ <;> simp [oldPart, incidentLoad]
  have hdisj : Disjoint (E.lib.image Sum.inl)
      ((E.relIdx pw0).image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr)) := by
    rw [disjoint_left]
    intro j h1 h2
    obtain ⟨i, -, rfl⟩ := mem_image.mp h1
    simp only [mem_union, mem_image, Function.comp_apply] at h2
    rcases h2 with ⟨r, -, h⟩ | ⟨h', -, h⟩ <;> simp at h
  rw [sum_union hdisj, hrest, add_zero, sum_image (fun a _ b _ h => Sum.inl_injective h)]
  rfl

theorem card_filter_idsPar_le (t : Tok κ) :
    (E.lib.filter fun i => t ∈ E.idsPar pw0 i).card ≤ 1 := by
  refine card_le_one.mpr fun i hi i' hi' => ?_
  obtain ⟨hi1, ht1⟩ := mem_filter.mp hi
  obtain ⟨hi2, ht2⟩ := mem_filter.mp hi'
  simp only [idsPar, mem_union, mem_image, mem_range] at ht1 ht2
  rcases ht1 with ⟨k, hk, h1⟩ | ⟨k, hk, h1⟩ <;> rcases ht2 with ⟨k', hk', h2⟩ | ⟨k', hk', h2⟩
  · rw [← h2] at h1
    simp only [Tok.vm.injEq] at h1
    have := E.slot_inj pw0 (E.mem_D_false pw0 hi1 hk) (E.mem_D_false pw0 hi2 hk') h1
    simp only [Prod.mk.injEq] at this
    exact this.1
  · rw [← h2] at h1; simp at h1
  · rw [← h2] at h1; simp at h1
  · rw [← h2] at h1
    simp only [Tok.pp.injEq] at h1
    exact h1.1

theorem card_filter_idsRel_le (t : Tok κ) :
    ((E.relIdx pw0).filter fun r => t ∈ E.idsRel pw0 r).card ≤ 1 := by
  refine card_le_one.mpr fun r hr r' hr' => ?_
  obtain ⟨hr1, ht1⟩ := mem_filter.mp hr
  obtain ⟨hr2, ht2⟩ := mem_filter.mp hr'
  obtain ⟨hi, hk⟩ := (E.mem_relIdx pw0).mp hr1
  obtain ⟨hi', hk'⟩ := (E.mem_relIdx pw0).mp hr2
  simp only [idsRel, mem_insert, mem_singleton] at ht1 ht2
  rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2 <;> rw [h2] at h1
  · simp only [Tok.pp.injEq] at h1
    exact Prod.ext h1.1.symm h1.2.symm
  · simp at h1
  · simp at h1
  · simp only [Tok.vm.injEq] at h1
    have := E.slot_inj pw0 (E.mem_D_true pw0 hi' hk') (E.mem_D_true pw0 hi hk) h1
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1.symm this.2.1.symm

theorem card_filter_idsMt_le {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hdx : ∀ x, (H.filter fun h => h.1 = x).card ≤ 24)
    (hdy : ∀ y, (H.filter fun h => h.2 = y).card ≤ 18) (t : Tok κ) :
    (H.filter fun h => t ∈ (idsMt h : Finset (Tok κ))).card ≤ 42 := by
  have hsub : (H.filter fun h => t ∈ (idsMt h : Finset (Tok κ))) ⊆
      (H.filter fun h => Tok.bp h.1 = t) ∪ (H.filter fun h => minusId h.2 = t) := by
    intro h hh
    obtain ⟨hh1, ht⟩ := mem_filter.mp hh
    simp only [idsMt, mem_insert, mem_singleton] at ht
    rcases ht with h1 | h1
    · exact mem_union_left _ (mem_filter.mpr ⟨hh1, h1.symm⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hh1, h1.symm⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 : (H.filter fun h => Tok.bp h.1 = t).card ≤ 24 := by
    rcases t with _ | _ | x | _
    · simp
    · simp
    · refine le_trans (card_le_card fun h hh => ?_) (hdx x)
      obtain ⟨hh, he⟩ := mem_filter.mp hh
      exact mem_filter.mpr ⟨hh, by simpa using he⟩
    · simp
  have h2 : (H.filter fun h => minusId h.2 = t).card ≤ 18 := by
    by_cases ht : ∃ y, minusId y = t
    · obtain ⟨y, rfl⟩ := ht
      refine le_trans (card_le_card fun h hh => ?_) (hdy y)
      obtain ⟨hh, he⟩ := mem_filter.mp hh
      exact mem_filter.mpr ⟨hh, minusId_injective he⟩
    · push Not at ht
      rw [card_eq_zero.mpr]
      · omega
      · exact filter_eq_empty_iff.mpr fun h _ => ht h.2
  omega

theorem sum_inr_load {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hdx : ∀ x, (H.filter fun h => h.1 = x).card ≤ 24)
    (hdy : ∀ y, (H.filter fun h => h.2 = y).card ≤ 18) (t : Tok κ) (a : Fin 8) :
    ∑ j ∈ E.indices pw0 H, incidentLoad (E.Bt pw0 j) (Sum.inr (t, a)) ≤ 88 := by
  simp only [Bt, incidentLoad_piece_inr]
  have h1 : ∑ j ∈ E.indices pw0 H,
      (if t ∈ E.ids pw0 j then incidentLoad (gadget t.sign) a else 0) ≤
      ∑ j ∈ E.indices pw0 H, (if t ∈ E.ids pw0 j then 2 else 0) :=
    sum_le_sum fun j _ => by
      split_ifs
      · exact gadget_incidentLoad_le _ _
      · exact le_rfl
  refine h1.trans ?_
  rw [← sum_filter, sum_const, smul_eq_mul]
  have hcount : ((E.indices pw0 H).filter fun j => t ∈ E.ids pw0 j).card ≤ 44 := by
    unfold indices
    rw [filter_union, filter_union]
    refine (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
      (Nat.add_le_add ?_ ?_)) ?_) |>.trans (by norm_num : 1 + 1 + 42 ≤ 44)
    · rw [filter_image]
      exact card_image_le.trans (E.card_filter_idsPar_le pw0 t)
    · rw [filter_image]
      exact card_image_le.trans (E.card_filter_idsRel_le pw0 t)
    · rw [filter_image]
      exact card_image_le.trans (card_filter_idsMt_le hdx hdy t)
  omega

theorem card_le_of_fst {H : Finset (ℕ × (ℕ ⊕ ℕ))} {n : ℕ} (hfst : ∀ h ∈ H, h.1 < n)
    (hdx : ∀ x, (H.filter fun h => h.1 = x).card ≤ 24) : H.card ≤ 24 * n := by
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := range n)
    (fun h hh => mem_range.mpr (hfst h hh))]
  calc ∑ x ∈ range n, (H.filter fun h => h.1 = x).card ≤ ∑ _x ∈ range n, 24 :=
        sum_le_sum fun x _ => hdx x
    _ = 24 * n := by rw [sum_const, card_range, smul_eq_mul, mul_comm]

/-! ### The main theorem -/

/-- **Charge layer.** -/
theorem charge_layer : ∃ (indices : Finset (JIdx κ)) (R : Finset (Sym2 (W1 W0 κ))),
    Disjoint R (liftE X0) ∧
    RefinerAssembly.RefinesReserve (p := pw1 pw0) (F := F0) indices (E.Bt pw0) (liftE X0) R ∧
    (∀ j ∈ indices, IsIntDiv (pw1 pw0) F0 (E.Bt pw0 j) ∧ (∀ e ∈ E.Bt pw0 j, ¬ e.IsDiag) ∧
      E.Bt pw0 j ⊆ R ∪ liftE X0 ∧ (E.Bt pw0 j).card ≤ 9 * (E.oldPart j).card + 16) ∧
    (∀ w, ∑ j ∈ indices, incidentLoad (E.Bt pw0 j) (Sum.inl w) =
      ∑ i ∈ E.lib, incidentLoad (E.P i) w) ∧
    (∀ t a, ∑ j ∈ indices, incidentLoad (E.Bt pw0 j) (Sum.inr (t, a)) ≤ 88) ∧
    indices.card ≤ E.lib.card + 97 * ∑ i ∈ E.lib, (E.P i).card := by
  -- the parity selection of the empty leftover bounds the number of present slots
  obtain ⟨T0, hT0, hdis0, hU0⟩ := E.refines ∅ (empty_subset _) (fun w => by
    simp [incidentLoad])
  have hs : E.sNum pw0 ≤ E.z pw0 := by
    rw [← E.card_Zs_eq pw0 hT0 hdis0 (empty_subset _) (charge_empty _ _) hU0, card_Zs pw0 E hT0]
    exact card_le_card (E.Zd_subset pw0 hT0)
  -- the robust graph is fixed before any leftover
  obtain ⟨m, H, hm, hHfst, hHsnd, hdx, hdy, hmatch⟩ := exists_robust (E.z pw0) (E.sNum pw0) hs
  refine ⟨E.indices pw0 H, E.Rt pw0 m, ?_, ?_, ?_, fun w => E.sum_inl_load pw0 w,
    fun t a => E.sum_inr_load pw0 hdx hdy t a, ?_⟩
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

end PartitionedTriangleAbsorption.TypedRefinerF0
