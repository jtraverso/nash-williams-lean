/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeLayerDefs

/-! # The charge layer: the selection for one leftover

Fix a parity selection `T` and a perfect matching `f` of the robust graph onto the fixed
minus buffer and the present variable slots `Zs T`. The selected typed pieces are the parity
pieces of `T` (with their tokens), the release pieces of the negative pieces outside `T` and
the matching pieces `{bp x, minus (f x)}`.

Every token identity has a unique *owner* among the selected pieces (`own`), which gives
pairwise disjointness; and the selected token identities are exactly all identities of the
remainder (`biUnion_ids_sel`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge

variable {W0 : Type*} [DecidableEq W0] {κ : Type*} [DecidableEq κ]

namespace EvenRefiner

variable {X0 : Finset (Sym2 W0)} (pw0 : W0 → Fin 2) (E : EvenRefiner κ X0)

/-- Present variable descriptors for the parity selection `T`. -/
noncomputable def Zd (T : Finset κ) : Finset (κ × ℕ × Bool) :=
  (E.lib \ T).biUnion (fun i => (range (E.mc pw0 i)).image fun k => (i, k, false)) ∪
    T.biUnion (fun i => (range (E.pc pw0 i)).image fun k => (i, k, true))

/-- Present variable slots. -/
noncomputable def Zs (T : Finset κ) : Finset ℕ := (E.Zd pw0 T).image (E.slot pw0)

/-- Selected release pieces. -/
noncomputable def relSel (T : Finset κ) : Finset (κ × ℕ) :=
  (E.lib \ T).biUnion fun i => (range (E.pc pw0 i)).image fun k => (i, k)

/-- The selected library indices. -/
noncomputable def sel (T : Finset κ) (n : ℕ) (f : ℕ → ℕ ⊕ ℕ) : Finset (JIdx κ) :=
  T.image Sum.inl ∪ (E.relSel pw0 T).image (Sum.inr ∘ Sum.inl) ∪
    (range n).image fun x => Sum.inr (Sum.inr (x, f x))

theorem mem_Zd {T : Finset κ} (hT : T ⊆ E.lib) {d : κ × ℕ × Bool} :
    d ∈ E.Zd pw0 T ↔ d ∈ E.D pw0 ∧ ((d.2.2 = false ∧ d.1 ∉ T) ∨ (d.2.2 = true ∧ d.1 ∈ T)) := by
  rcases d with ⟨i, k, b⟩
  rw [mem_D]
  simp only [Zd, mem_union, mem_biUnion, mem_sdiff, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro (⟨i', ⟨hi', hT'⟩, k', hk', rfl, rfl, rfl⟩ | ⟨i', hi', k', hk', rfl, rfl, rfl⟩)
    · exact ⟨⟨hi', Or.inl ⟨rfl, hk'⟩⟩, Or.inl ⟨rfl, hT'⟩⟩
    · exact ⟨⟨hT hi', Or.inr ⟨rfl, hk'⟩⟩, Or.inr ⟨rfl, hi'⟩⟩
  · rintro ⟨⟨hi, hk⟩, hc⟩
    rcases hc with ⟨rfl, hiT⟩ | ⟨rfl, hiT⟩
    · exact Or.inl ⟨i, ⟨hi, hiT⟩, k, by simpa using hk, rfl, rfl, rfl⟩
    · exact Or.inr ⟨i, hiT, k, by simpa using hk, rfl, rfl, rfl⟩

theorem Zd_subset {T : Finset κ} (hT : T ⊆ E.lib) : E.Zd pw0 T ⊆ E.D pw0 :=
  fun _ hd => ((E.mem_Zd pw0 hT).mp hd).1

theorem Zs_subset {T : Finset κ} (hT : T ⊆ E.lib) : E.Zs pw0 T ⊆ range (E.z pw0) := by
  intro j hj
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hj
  exact mem_range.mpr (E.slot_lt pw0 (E.Zd_subset pw0 hT hd))

theorem mem_relSel {T : Finset κ} {r : κ × ℕ} :
    r ∈ E.relSel pw0 T ↔ r.1 ∈ E.lib ∧ r.1 ∉ T ∧ r.2 < E.pc pw0 r.1 := by
  rcases r with ⟨i, k⟩
  simp only [relSel, mem_biUnion, mem_sdiff, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i', ⟨hi', hT'⟩, k', hk', rfl, rfl⟩; exact ⟨hi', hT', hk'⟩
  · rintro ⟨hi, hT, hk⟩; exact ⟨i, ⟨hi, hT⟩, k, hk, rfl, rfl⟩

/-- The descriptor at a slot. -/
noncomputable def descAt (j : ℕ) : Option (κ × ℕ × Bool) :=
  if h : ∃ d ∈ E.D pw0, E.slot pw0 d = j then some (Classical.choose h) else none

theorem descAt_slot {d : κ × ℕ × Bool} (hd : d ∈ E.D pw0) :
    E.descAt pw0 (E.slot pw0 d) = some d := by
  have h : ∃ d' ∈ E.D pw0, E.slot pw0 d' = E.slot pw0 d := ⟨d, hd, rfl⟩
  unfold descAt
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  rw [E.slot_inj pw0 h1 hd h2]

/-- Inverse of the matching on its domain. -/
noncomputable def finv (n : ℕ) (f : ℕ → ℕ ⊕ ℕ) (y : ℕ ⊕ ℕ) : ℕ :=
  if h : ∃ x < n, f x = y then Classical.choose h else 0

theorem finv_apply {n : ℕ} {f : ℕ → ℕ ⊕ ℕ} (hf : Set.InjOn f (range n)) {x : ℕ} (hx : x < n) :
    finv n f (f x) = x := by
  have h : ∃ x' < n, f x' = f x := ⟨x, hx, rfl⟩
  unfold finv
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  exact hf (mem_coe.mpr (mem_range.mpr h1)) (mem_coe.mpr (mem_range.mpr hx)) h2

/-- The matching piece covering a minus vertex. -/
noncomputable def mtOwner (n : ℕ) (f : ℕ → ℕ ⊕ ℕ) (y : ℕ ⊕ ℕ) : JIdx κ :=
  Sum.inr (Sum.inr (finv n f y, y))

/-- The owner of a token identity. -/
noncomputable def own (T : Finset κ) (n : ℕ) (f : ℕ → ℕ ⊕ ℕ) : Tok κ → JIdx κ
  | Tok.pp i k => if i ∈ T then Sum.inl i else Sum.inr (Sum.inl (i, k))
  | Tok.vm j =>
    match E.descAt pw0 j with
    | some (i, _, false) => if i ∈ T then Sum.inl i else mtOwner n f (Sum.inr j)
    | some (i, k, true) => if i ∈ T then mtOwner n f (Sum.inr j) else Sum.inr (Sum.inl (i, k))
    | none => mtOwner n f (Sum.inr j)
  | Tok.bp x => Sum.inr (Sum.inr (x, f x))
  | Tok.bm y => mtOwner n f (Sum.inl y)

section Selection

variable {T : Finset κ} (hT : T ⊆ E.lib) {m : ℕ} {f : ℕ → ℕ ⊕ ℕ}
  (hinj : Set.InjOn f (range (m + E.sNum pw0)))
  (himg : (range (m + E.sNum pw0)).image f = (range m).disjSum (E.Zs pw0 T))

include hT hinj himg

theorem own_spec : ∀ j ∈ E.sel pw0 T (m + E.sNum pw0) f, ∀ t ∈ E.ids pw0 j,
    E.own pw0 T (m + E.sNum pw0) f t = j := by
  intro j hj t ht
  simp only [sel, mem_union, mem_image, Function.comp_apply] at hj
  rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨x, hx, rfl⟩
  · simp only [ids, idsPar, mem_union, mem_image, mem_range] at ht
    rcases ht with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · simp only [own]
      rw [E.descAt_slot pw0 (E.mem_D_false pw0 (hT hi) hk)]
      simp [hi]
    · simp [own, hi]
  · obtain ⟨hi, hiT, hk⟩ := (E.mem_relSel pw0).mp hr
    simp only [ids, idsRel, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · simp [own, hiT]
    · simp only [own]
      rw [E.descAt_slot pw0 (E.mem_D_true pw0 hi hk)]
      simp [hiT]
  · have hx' := mem_range.mp hx
    simp only [ids, idsMt, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · rfl
    · have hfx : f x ∈ (range m).disjSum (E.Zs pw0 T) := by
        rw [← himg]; exact mem_image_of_mem f hx
      have hown : mtOwner (κ := κ) (m + E.sNum pw0) f (f x) = Sum.inr (Sum.inr (x, f x)) := by
        simp only [mtOwner, finv_apply hinj hx']
      rcases hfy : f x with y | j'
      · simp only [minusId, own]
        rw [← hfy, hown]
      · rw [hfy] at hfx hown
        have hfx' : j' ∈ E.Zs pw0 T := by simpa using hfx
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hfx'
        obtain ⟨hdD, hdc⟩ := (E.mem_Zd pw0 hT).mp hd
        simp only [minusId, own]
        rw [E.descAt_slot pw0 hdD]
        rcases d with ⟨i, k, b⟩
        rcases hdc with ⟨hb, hiT⟩ | ⟨hb, hiT⟩ <;> simp only at hb hiT <;> subst hb
        · simp only [hiT, ite_false]; rw [hown]
        · simp only [hiT, ite_true]; rw [hown]

theorem pairwiseDisjoint_ids :
    ((E.sel pw0 T (m + E.sNum pw0) f : Finset (JIdx κ)) : Set (JIdx κ)).PairwiseDisjoint
      (E.ids pw0) := by
  intro j hj j' hj' hne
  rw [Function.onFun, disjoint_left]
  intro t ht ht'
  exact hne ((E.own_spec pw0 hT hinj himg j hj t ht).symm.trans
    (E.own_spec pw0 hT hinj himg j' hj' t ht'))

omit hT hinj himg in
theorem pairwiseDisjoint_oldPart (hdisT : (T : Set κ).PairwiseDisjoint E.P) {n : ℕ}
    {f : ℕ → ℕ ⊕ ℕ} :
    ((E.sel pw0 T n f : Finset (JIdx κ)) : Set (JIdx κ)).PairwiseDisjoint E.oldPart := by
  intro j hj j' hj' hne
  rw [Function.onFun]
  rcases j with i | j <;> rcases j' with i' | j'
  · have hi : i ∈ T := by
      simpa [sel] using hj
    have hi' : i' ∈ T := by
      simpa [sel] using hj'
    exact hdisT hi hi' (fun h => hne (by rw [h]))
  · exact disjoint_empty_right _
  · exact disjoint_empty_left _
  · exact disjoint_empty_left _

omit hT hinj himg in
theorem biUnion_oldPart_sel {n : ℕ} {f : ℕ → ℕ ⊕ ℕ} :
    (E.sel pw0 T n f).biUnion E.oldPart = T.biUnion E.P := by
  ext e
  simp only [mem_biUnion, sel, mem_union, mem_image, Function.comp_apply]
  constructor
  · rintro ⟨j, (⟨i, hi, rfl⟩ | ⟨r, -, rfl⟩) | ⟨x, -, rfl⟩, he⟩
    · exact ⟨i, hi, he⟩
    · simp [oldPart] at he
    · simp [oldPart] at he
  · rintro ⟨i, hi, he⟩
    exact ⟨Sum.inl i, Or.inl (Or.inl ⟨i, hi, rfl⟩), he⟩

omit hinj in
theorem biUnion_ids_sel :
    (E.sel pw0 T (m + E.sNum pw0) f).biUnion (E.ids pw0) = E.allIds pw0 m := by
  have hfmem : ∀ x < m + E.sNum pw0, f x ∈ (range m).disjSum (E.Zs pw0 T) := by
    intro x hx; rw [← himg]; exact mem_image_of_mem f (mem_range.mpr hx)
  have hsurj : ∀ y ∈ (range m).disjSum (E.Zs pw0 T), ∃ x < m + E.sNum pw0, f x = y := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact ⟨x, mem_range.mp hx, rfl⟩
  have hmt : ∀ x < m + E.sNum pw0,
      Sum.inr (Sum.inr (x, f x)) ∈ E.sel pw0 T (m + E.sNum pw0) f := by
    intro x hx
    exact mem_union_right _ (mem_image.mpr ⟨x, mem_range.mpr hx, rfl⟩)
  ext t
  simp only [mem_biUnion]
  constructor
  · rintro ⟨j, hj, ht⟩
    simp only [sel, mem_union, mem_image, Function.comp_apply] at hj
    simp only [allIds, mem_union, mem_image, mem_range]
    rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨x, hx, rfl⟩
    · simp only [ids, idsPar, mem_union, mem_image, mem_range] at ht
      rcases ht with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
      · exact Or.inl (Or.inl (Or.inr ⟨_, E.slot_lt pw0 (E.mem_D_false pw0 (hT hi) hk), rfl⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨(i, k), (E.mem_relIdx pw0).mpr ⟨hT hi, hk⟩, rfl⟩))
    · obtain ⟨hi, -, hk⟩ := (E.mem_relSel pw0).mp hr
      simp only [ids, idsRel, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (Or.inl (Or.inl ⟨r, (E.mem_relIdx pw0).mpr ⟨hi, hk⟩, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨_, E.slot_lt pw0 (E.mem_D_true pw0 hi hk), rfl⟩))
    · have hx' := mem_range.mp hx
      simp only [ids, idsMt, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (Or.inr ⟨x, hx', rfl⟩)
      · have := hfmem x hx'
        rcases hfx : f x with y | j'
        · rw [hfx] at this
          have : y < m := by simpa using this
          exact Or.inr ⟨y, this, rfl⟩
        · rw [hfx] at this
          have : j' ∈ E.Zs pw0 T := by simpa using this
          exact Or.inl (Or.inl (Or.inr ⟨j', mem_range.mp (E.Zs_subset pw0 hT this), rfl⟩))
  · intro ht
    simp only [allIds, mem_union, mem_image, mem_range] at ht
    rcases ht with ((⟨r, hr, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩
    · obtain ⟨hi, hk⟩ := (E.mem_relIdx pw0).mp hr
      by_cases hiT : r.1 ∈ T
      · refine ⟨Sum.inl r.1, mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hiT)), ?_⟩
        simp only [ids, idsPar]
        exact mem_union_right _ (mem_image.mpr ⟨r.2, mem_range.mpr hk, rfl⟩)
      · refine ⟨Sum.inr (Sum.inl r), mem_union_left _ (mem_union_right _
          (mem_image.mpr ⟨r, (E.mem_relSel pw0).mpr ⟨hi, hiT, hk⟩, rfl⟩)), ?_⟩
        simp [ids, idsRel]
    · obtain ⟨d, hd, rfl⟩ := UniversalRefiner.exists_pos_eq hj
      change E.slot pw0 d < _ at hj
      obtain ⟨hi, hdc⟩ := (E.mem_D pw0).mp hd
      rcases d with ⟨i, k, b⟩
      have hviaMatch : (i, k, b) ∈ E.Zd pw0 T →
          ∃ a ∈ E.sel pw0 T (m + E.sNum pw0) f,
            Tok.vm (UniversalRefiner.pos (E.D pw0) (i, k, b)) ∈ E.ids pw0 a := by
        intro hZ
        have : Sum.inr (E.slot pw0 (i, k, b)) ∈ (range m).disjSum (E.Zs pw0 T) := by
          rw [mem_disjSum]; exact Or.inr ⟨_, mem_image_of_mem _ hZ, rfl⟩
        obtain ⟨x, hx, hfx⟩ := hsurj _ this
        refine ⟨_, hmt x hx, ?_⟩
        simp only [ids, idsMt, hfx, minusId, mem_insert, mem_singleton]
        exact Or.inr rfl
      rcases hdc with ⟨hb, hk⟩ | ⟨hb, hk⟩ <;> simp only at hb hk hi <;> subst hb
      · by_cases hiT : i ∈ T
        · refine ⟨Sum.inl i, mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hiT)), ?_⟩
          simp only [ids, idsPar]
          exact mem_union_left _ (mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩)
        · exact hviaMatch ((E.mem_Zd pw0 hT).mpr ⟨hd, Or.inl ⟨rfl, hiT⟩⟩)
      · by_cases hiT : i ∈ T
        · exact hviaMatch ((E.mem_Zd pw0 hT).mpr ⟨hd, Or.inr ⟨rfl, hiT⟩⟩)
        · refine ⟨Sum.inr (Sum.inl (i, k)), mem_union_left _ (mem_union_right _
            (mem_image.mpr ⟨(i, k), (E.mem_relSel pw0).mpr ⟨hi, hiT, hk⟩, rfl⟩)), ?_⟩
          simp only [ids, idsRel, mem_insert, mem_singleton]
          exact Or.inr rfl
    · exact ⟨_, hmt x hx, by simp [ids, idsMt]⟩
    · have : (Sum.inl y : ℕ ⊕ ℕ) ∈ (range m).disjSum (E.Zs pw0 T) := by
        rw [mem_disjSum]; exact Or.inl ⟨y, mem_range.mpr hy, rfl⟩
      obtain ⟨x, hx, hfx⟩ := hsurj _ this
      refine ⟨_, hmt x hx, ?_⟩
      simp [ids, idsMt, hfx, minusId]

end Selection

end EvenRefiner

end PartitionedTriangleAbsorption.TypedRefinerF0
