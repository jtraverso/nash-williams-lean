/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeLayer

/-! # Token bookkeeping for an integer charge, independent of any host

A *ledger* is a finite library `lib` with an integer token demand `c i` for every piece:
`mc i = max(c i, 0)` minus tokens and `pc i = max(-c i, 0)` plus tokens. This module
reproduces, for an arbitrary demand function, the purely combinatorial token selection of the
accepted F0 charge layer (`TypedRefinerF0.ChargeLayerDefs`/`ChargeLayerSelect`): the token
identities, the variable slots, the release and matching pieces, and the owner map showing that
for every parity selection `T` and every perfect matching `f` of the robust graph, the selected
token identities are pairwise disjoint and exactly exhaust all token identities.

No graph, host or charge appears here; the token identities are later realized physically.
The token type `Tok`, `minusId`, `idsMt`, `JIdx` and the robust graph `exists_robust` are reused
from the accepted modules unchanged.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3

open Finset TypedRefinerF0

/-- A finite library with an integer token demand per piece. -/
structure Ledger (κ : Type*) where
  lib : Finset κ
  c : κ → ℤ

namespace Ledger

variable {κ : Type*} [DecidableEq κ] (A : Ledger κ)

/-- Number of minus tokens of piece `i`. -/
def mc (i : κ) : ℕ := (A.c i).toNat

/-- Number of plus tokens of piece `i`. -/
def pc (i : κ) : ℕ := (-A.c i).toNat

/-- Descriptors of the variable minus tokens contributed by piece `i`. -/
def descOf (i : κ) : Finset (κ × ℕ × Bool) :=
  (range (A.mc i)).image (fun k => (i, k, false)) ∪
    (range (A.pc i)).image (fun k => (i, k, true))

/-- All variable descriptors. -/
def D : Finset (κ × ℕ × Bool) := A.lib.biUnion A.descOf

/-- The slot of a descriptor. -/
noncomputable def slot (d : κ × ℕ × Bool) : ℕ := UniversalRefiner.pos A.D d

/-- Number of variable slots. -/
def z : ℕ := A.D.card

/-- Number of present slots for a conserved total demand `K`. -/
def sNum (K : ℤ) : ℕ := ((∑ i ∈ A.lib, (A.mc i : ℤ)) - K).toNat

/-- Token identities of the parity piece `i`. -/
noncomputable def idsPar (i : κ) : Finset (Tok κ) :=
  (range (A.mc i)).image (fun k => Tok.vm (A.slot (i, k, false))) ∪
    (range (A.pc i)).image (fun k => Tok.pp i k)

/-- Token identities of the release piece of `pp i k`. -/
noncomputable def idsRel (r : κ × ℕ) : Finset (Tok κ) :=
  {Tok.pp r.1 r.2, Tok.vm (A.slot (r.1, r.2, true))}

/-- Token identities of a library index. -/
noncomputable def ids : JIdx κ → Finset (Tok κ)
  | Sum.inl i => A.idsPar i
  | Sum.inr (Sum.inl r) => A.idsRel r
  | Sum.inr (Sum.inr h) => idsMt h

/-- Release indices. -/
def relIdx : Finset (κ × ℕ) :=
  A.lib.biUnion fun i => (range (A.pc i)).image fun k => (i, k)

/-- The library for a robust graph `H`. -/
def indices (H : Finset (ℕ × (ℕ ⊕ ℕ))) : Finset (JIdx κ) :=
  A.lib.image Sum.inl ∪ A.relIdx.image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr)

/-- All token identities of the remainder (`n` plus buffers, `m` minus buffers). -/
def allIds (n m : ℕ) : Finset (Tok κ) :=
  A.relIdx.image (fun r => Tok.pp r.1 r.2) ∪ (range A.z).image Tok.vm ∪
    (range n).image Tok.bp ∪ (range m).image Tok.bm

theorem mem_D {d : κ × ℕ × Bool} :
    d ∈ A.D ↔ d.1 ∈ A.lib ∧ ((d.2.2 = false ∧ d.2.1 < A.mc d.1) ∨
      (d.2.2 = true ∧ d.2.1 < A.pc d.1)) := by
  rcases d with ⟨i, k, b⟩
  simp only [D, descOf, mem_biUnion, mem_union, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', (⟨k', hk', rfl, rfl, rfl⟩ | ⟨k', hk', rfl, rfl, rfl⟩)⟩
    · exact ⟨hi', Or.inl ⟨rfl, hk'⟩⟩
    · exact ⟨hi', Or.inr ⟨rfl, hk'⟩⟩
  · rintro ⟨hi, (⟨rfl, hk⟩ | ⟨rfl, hk⟩)⟩
    · exact ⟨i, hi, Or.inl ⟨k, hk, rfl, rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inr ⟨k, hk, rfl, rfl, rfl⟩⟩

theorem mem_D_false {i : κ} {k : ℕ} (hi : i ∈ A.lib) (hk : k < A.mc i) :
    (i, k, false) ∈ A.D :=
  (A.mem_D).mpr ⟨hi, Or.inl ⟨rfl, hk⟩⟩

theorem mem_D_true {i : κ} {k : ℕ} (hi : i ∈ A.lib) (hk : k < A.pc i) :
    (i, k, true) ∈ A.D :=
  (A.mem_D).mpr ⟨hi, Or.inr ⟨rfl, hk⟩⟩

theorem slot_inj {d d' : κ × ℕ × Bool} (hd : d ∈ A.D) (hd' : d' ∈ A.D)
    (h : A.slot d = A.slot d') : d = d' :=
  UniversalRefiner.pos_inj hd hd' h

theorem slot_lt {d : κ × ℕ × Bool} (hd : d ∈ A.D) : A.slot d < A.z :=
  UniversalRefiner.pos_lt hd

theorem mem_relIdx {r : κ × ℕ} : r ∈ A.relIdx ↔ r.1 ∈ A.lib ∧ r.2 < A.pc r.1 := by
  rcases r with ⟨i, k⟩
  simp only [relIdx, mem_biUnion, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', k', hk', rfl, rfl⟩; exact ⟨hi', hk'⟩
  · rintro ⟨hi, hk⟩; exact ⟨i, hi, k, hk, rfl, rfl⟩

omit [DecidableEq κ] in
theorem c_eq (i : κ) : A.c i = (A.mc i : ℤ) - A.pc i :=
  (Int.toNat_sub_toNat_neg _).symm

omit [DecidableEq κ] in
theorem mc_add_pc (i : κ) : A.mc i + A.pc i = (A.c i).natAbs := by
  unfold mc pc; omega

theorem card_descOf (i : κ) : (A.descOf i).card = A.mc i + A.pc i := by
  unfold descOf
  rw [card_union_of_disjoint]
  · rw [card_image_of_injective _ (fun a b h => by simpa using h),
      card_image_of_injective _ (fun a b h => by simpa using h), card_range, card_range]
  · rw [disjoint_left]
    intro d h1 h2
    obtain ⟨k, -, rfl⟩ := mem_image.mp h1
    obtain ⟨k', -, h⟩ := mem_image.mp h2
    simp at h

theorem z_eq : A.z = ∑ i ∈ A.lib, (A.c i).natAbs := by
  unfold z D
  rw [card_biUnion]
  · exact sum_congr rfl fun i _ => (A.card_descOf i).trans (A.mc_add_pc i)
  · intro i _ i' _ hii'
    rw [Function.onFun, disjoint_left]
    intro d h1 h2
    simp only [descOf, mem_union, mem_image] at h1 h2
    rcases h1 with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;>
      rcases h2 with ⟨k', -, h⟩ | ⟨k', -, h⟩ <;> simp_all

theorem card_relIdx : A.relIdx.card = ∑ i ∈ A.lib, A.pc i := by
  unfold relIdx
  rw [card_biUnion]
  · refine sum_congr rfl fun i _ => ?_
    rw [card_image_of_injective _ (fun a b h => by simpa using h), card_range]
  · intro i _ i' _ hii'
    rw [Function.onFun, disjoint_left]
    intro r h1 h2
    obtain ⟨k, -, rfl⟩ := mem_image.mp h1
    obtain ⟨k', -, h⟩ := mem_image.mp h2
    simp only [Prod.mk.injEq] at h
    exact hii' h.1.symm

theorem card_relIdx_le : A.relIdx.card ≤ A.z := by
  rw [card_relIdx, z_eq]
  exact sum_le_sum fun i _ => by rw [← A.mc_add_pc i]; omega

theorem card_allIds_le (n m : ℕ) : (A.allIds n m).card ≤ 2 * A.z + n + m := by
  unfold allIds
  refine (card_union_le _ _).trans ?_
  refine (Nat.add_le_add_right ((card_union_le _ _).trans (Nat.add_le_add_right
    (card_union_le _ _) _)) _).trans ?_
  have h1 := A.card_relIdx_le
  have h2 : ((A.relIdx).image (fun r => Tok.pp r.1 r.2) : Finset (Tok κ)).card ≤ A.z :=
    card_image_le.trans h1
  have h3 : ((range A.z).image Tok.vm : Finset (Tok κ)).card ≤ A.z :=
    card_image_le.trans (by simp)
  have h4 : ((range n).image Tok.bp : Finset (Tok κ)).card ≤ n := card_image_le.trans (by simp)
  have h5 : ((range m).image Tok.bm : Finset (Tok κ)).card ≤ m := card_image_le.trans (by simp)
  omega

/-! ### The selection for one parity selection `T` -/

/-- Present variable descriptors for the parity selection `T`. -/
def Zd (T : Finset κ) : Finset (κ × ℕ × Bool) :=
  (A.lib \ T).biUnion (fun i => (range (A.mc i)).image fun k => (i, k, false)) ∪
    T.biUnion (fun i => (range (A.pc i)).image fun k => (i, k, true))

/-- Present variable slots. -/
noncomputable def Zs (T : Finset κ) : Finset ℕ := (A.Zd T).image A.slot

/-- Selected release pieces. -/
def relSel (T : Finset κ) : Finset (κ × ℕ) :=
  (A.lib \ T).biUnion fun i => (range (A.pc i)).image fun k => (i, k)

/-- The selected library indices. -/
def sel (T : Finset κ) (n : ℕ) (f : ℕ → ℕ ⊕ ℕ) : Finset (JIdx κ) :=
  T.image Sum.inl ∪ (A.relSel T).image (Sum.inr ∘ Sum.inl) ∪
    (range n).image fun x => Sum.inr (Sum.inr (x, f x))

theorem mem_Zd {T : Finset κ} (hT : T ⊆ A.lib) {d : κ × ℕ × Bool} :
    d ∈ A.Zd T ↔ d ∈ A.D ∧ ((d.2.2 = false ∧ d.1 ∉ T) ∨ (d.2.2 = true ∧ d.1 ∈ T)) := by
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

theorem Zd_subset {T : Finset κ} (hT : T ⊆ A.lib) : A.Zd T ⊆ A.D :=
  fun _ hd => ((A.mem_Zd hT).mp hd).1

theorem Zs_subset {T : Finset κ} (hT : T ⊆ A.lib) : A.Zs T ⊆ range A.z := by
  intro j hj
  obtain ⟨d, hd, rfl⟩ := mem_image.mp hj
  exact mem_range.mpr (A.slot_lt (A.Zd_subset hT hd))

theorem mem_relSel {T : Finset κ} {r : κ × ℕ} :
    r ∈ A.relSel T ↔ r.1 ∈ A.lib ∧ r.1 ∉ T ∧ r.2 < A.pc r.1 := by
  rcases r with ⟨i, k⟩
  simp only [relSel, mem_biUnion, mem_sdiff, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i', ⟨hi', hT'⟩, k', hk', rfl, rfl⟩; exact ⟨hi', hT', hk'⟩
  · rintro ⟨hi, hT, hk⟩; exact ⟨i, ⟨hi, hT⟩, k, hk, rfl, rfl⟩

theorem card_Zd (T : Finset κ) :
    (A.Zd T).card = ∑ i ∈ A.lib \ T, A.mc i + ∑ i ∈ T, A.pc i := by
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

theorem card_Zs {T : Finset κ} (hT : T ⊆ A.lib) : (A.Zs T).card = (A.Zd T).card :=
  card_image_of_injOn fun _ hd _ hd' h =>
    A.slot_inj (A.Zd_subset hT hd) (A.Zd_subset hT hd') h

/-- **A conserved total demand fixes the number of present slots.** -/
theorem card_Zs_eq {T : Finset κ} (hT : T ⊆ A.lib) {K : ℤ} (hK : ∑ i ∈ T, A.c i = K) :
    (A.Zs T).card = A.sNum K := by
  rw [A.card_Zs hT, A.card_Zd T, sNum, ← hK]
  have hsplit : ∑ i ∈ A.lib, (A.mc i : ℤ) =
      ∑ i ∈ A.lib \ T, (A.mc i : ℤ) + ∑ i ∈ T, (A.mc i : ℤ) :=
    (sum_sdiff hT).symm
  have hchg : ∑ i ∈ T, A.c i = ∑ i ∈ T, ((A.mc i : ℤ) - A.pc i) :=
    sum_congr rfl fun i _ => A.c_eq i
  rw [hsplit, hchg, sum_sub_distrib]
  have : ∑ i ∈ A.lib \ T, (A.mc i : ℤ) + ∑ i ∈ T, (A.mc i : ℤ) -
      (∑ i ∈ T, (A.mc i : ℤ) - ∑ i ∈ T, (A.pc i : ℤ)) =
      ((∑ i ∈ A.lib \ T, A.mc i + ∑ i ∈ T, A.pc i : ℕ) : ℤ) := by
    push_cast; ring
  rw [this, Int.toNat_natCast]

/-- The descriptor at a slot. -/
noncomputable def descAt (j : ℕ) : Option (κ × ℕ × Bool) :=
  if h : ∃ d ∈ A.D, A.slot d = j then some (Classical.choose h) else none

theorem descAt_slot {d : κ × ℕ × Bool} (hd : d ∈ A.D) :
    A.descAt (A.slot d) = some d := by
  have h : ∃ d' ∈ A.D, A.slot d' = A.slot d := ⟨d, hd, rfl⟩
  unfold descAt
  rw [dite_eq_left h]
  obtain ⟨h1, h2⟩ := Classical.choose_spec h
  rw [A.slot_inj h1 hd h2]

/-- Inverse of the matching on its domain. -/
noncomputable def finv (n : ℕ) (f : ℕ → ℕ ⊕ ℕ) (y : ℕ ⊕ ℕ) : ℕ :=
  if h : ∃ x < n, f x = y then Classical.choose h else 0

omit [DecidableEq κ] in
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
    match A.descAt j with
    | some (i, _, false) => if i ∈ T then Sum.inl i else mtOwner n f (Sum.inr j)
    | some (i, k, true) => if i ∈ T then mtOwner n f (Sum.inr j) else Sum.inr (Sum.inl (i, k))
    | none => mtOwner n f (Sum.inr j)
  | Tok.bp x => Sum.inr (Sum.inr (x, f x))
  | Tok.bm y => mtOwner n f (Sum.inl y)

section Selection

variable {T : Finset κ} (hT : T ⊆ A.lib) {n m : ℕ} {f : ℕ → ℕ ⊕ ℕ}
  (hinj : Set.InjOn f (range n))
  (himg : (range n).image f = (range m).disjSum (A.Zs T))

include hT hinj himg

theorem own_spec : ∀ j ∈ A.sel T n f, ∀ t ∈ A.ids j, A.own T n f t = j := by
  intro j hj t ht
  simp only [sel, mem_union, mem_image, Function.comp_apply] at hj
  rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨x, hx, rfl⟩
  · simp only [ids, idsPar, mem_union, mem_image, mem_range] at ht
    rcases ht with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · simp only [own]
      rw [A.descAt_slot (A.mem_D_false (hT hi) hk)]
      simp [hi]
    · simp [own, hi]
  · obtain ⟨hi, hiT, hk⟩ := (A.mem_relSel).mp hr
    simp only [ids, idsRel, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · simp [own, hiT]
    · simp only [own]
      rw [A.descAt_slot (A.mem_D_true hi hk)]
      simp [hiT]
  · have hx' := mem_range.mp hx
    simp only [ids, idsMt, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · rfl
    · have hfx : f x ∈ (range m).disjSum (A.Zs T) := by
        rw [← himg]; exact mem_image_of_mem f hx
      have hown : mtOwner (κ := κ) n f (f x) = Sum.inr (Sum.inr (x, f x)) := by
        simp only [mtOwner, finv_apply hinj hx']
      rcases hfy : f x with y | j'
      · simp only [minusId, own]
        rw [← hfy, hown]
      · rw [hfy] at hfx hown
        have hfx' : j' ∈ A.Zs T := by simpa using hfx
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hfx'
        obtain ⟨hdD, hdc⟩ := (A.mem_Zd hT).mp hd
        simp only [minusId, own]
        rw [A.descAt_slot hdD]
        rcases d with ⟨i, k, b⟩
        rcases hdc with ⟨hb, hiT⟩ | ⟨hb, hiT⟩ <;> simp only at hb hiT <;> subst hb
        · simp only [hiT, ite_false]; rw [hown]
        · simp only [hiT, ite_true]; rw [hown]

theorem pairwiseDisjoint_ids :
    ((A.sel T n f : Finset (JIdx κ)) : Set (JIdx κ)).PairwiseDisjoint A.ids := by
  intro j hj j' hj' hne
  rw [Function.onFun, disjoint_left]
  intro t ht ht'
  exact hne ((A.own_spec hT hinj himg j hj t ht).symm.trans
    (A.own_spec hT hinj himg j' hj' t ht'))

omit hinj in
theorem biUnion_ids_sel : (A.sel T n f).biUnion A.ids = A.allIds n m := by
  have hfmem : ∀ x < n, f x ∈ (range m).disjSum (A.Zs T) := by
    intro x hx; rw [← himg]; exact mem_image_of_mem f (mem_range.mpr hx)
  have hsurj : ∀ y ∈ (range m).disjSum (A.Zs T), ∃ x < n, f x = y := by
    intro y hy
    rw [← himg] at hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact ⟨x, mem_range.mp hx, rfl⟩
  have hmt : ∀ x < n, Sum.inr (Sum.inr (x, f x)) ∈ A.sel T n f := by
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
      · exact Or.inl (Or.inl (Or.inr ⟨_, A.slot_lt (A.mem_D_false (hT hi) hk), rfl⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨(i, k), (A.mem_relIdx).mpr ⟨hT hi, hk⟩, rfl⟩))
    · obtain ⟨hi, -, hk⟩ := (A.mem_relSel).mp hr
      simp only [ids, idsRel, mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl
      · exact Or.inl (Or.inl (Or.inl ⟨r, (A.mem_relIdx).mpr ⟨hi, hk⟩, rfl⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨_, A.slot_lt (A.mem_D_true hi hk), rfl⟩))
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
          have : j' ∈ A.Zs T := by simpa using this
          exact Or.inl (Or.inl (Or.inr ⟨j', mem_range.mp (A.Zs_subset hT this), rfl⟩))
  · intro ht
    simp only [allIds, mem_union, mem_image, mem_range] at ht
    rcases ht with ((⟨r, hr, rfl⟩ | ⟨j, hj, rfl⟩) | ⟨x, hx, rfl⟩) | ⟨y, hy, rfl⟩
    · obtain ⟨hi, hk⟩ := (A.mem_relIdx).mp hr
      by_cases hiT : r.1 ∈ T
      · refine ⟨Sum.inl r.1, mem_union_left _ (mem_union_left _ (mem_image_of_mem _ hiT)), ?_⟩
        simp only [ids, idsPar]
        exact mem_union_right _ (mem_image.mpr ⟨r.2, mem_range.mpr hk, rfl⟩)
      · refine ⟨Sum.inr (Sum.inl r), mem_union_left _ (mem_union_right _
          (mem_image.mpr ⟨r, (A.mem_relSel).mpr ⟨hi, hiT, hk⟩, rfl⟩)), ?_⟩
        simp [ids, idsRel]
    · obtain ⟨d, hd, rfl⟩ := UniversalRefiner.exists_pos_eq hj
      change A.slot d < _ at hj
      obtain ⟨hi, hdc⟩ := (A.mem_D).mp hd
      rcases d with ⟨i, k, b⟩
      have hviaMatch : (i, k, b) ∈ A.Zd T →
          ∃ a ∈ A.sel T n f, Tok.vm (UniversalRefiner.pos A.D (i, k, b)) ∈ A.ids a := by
        intro hZ
        have : Sum.inr (A.slot (i, k, b)) ∈ (range m).disjSum (A.Zs T) := by
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
        · exact hviaMatch ((A.mem_Zd hT).mpr ⟨hd, Or.inl ⟨rfl, hiT⟩⟩)
      · by_cases hiT : i ∈ T
        · exact hviaMatch ((A.mem_Zd hT).mpr ⟨hd, Or.inr ⟨rfl, hiT⟩⟩)
        · refine ⟨Sum.inr (Sum.inl (i, k)), mem_union_left _ (mem_union_right _
            (mem_image.mpr ⟨(i, k), (A.mem_relSel).mpr ⟨hi, hiT, hk⟩, rfl⟩)), ?_⟩
          simp only [ids, idsRel, mem_insert, mem_singleton]
          exact Or.inr rfl
    · exact ⟨_, hmt x hx, by simp [ids, idsMt]⟩
    · have : (Sum.inl y : ℕ ⊕ ℕ) ∈ (range m).disjSum (A.Zs T) := by
        rw [mem_disjSum]; exact Or.inl ⟨y, mem_range.mpr hy, rfl⟩
      obtain ⟨x, hx, hfx⟩ := hsurj _ this
      refine ⟨_, hmt x hx, ?_⟩
      simp [ids, idsMt, hfx, minusId]

end Selection

theorem sel_subset_indices {T : Finset κ} (hT : T ⊆ A.lib) {n : ℕ} {f : ℕ → ℕ ⊕ ℕ}
    {H : Finset (ℕ × (ℕ ⊕ ℕ))} (hedge : ∀ x < n, (x, f x) ∈ H) :
    A.sel T n f ⊆ A.indices H := by
  intro j hj
  simp only [sel, mem_union, mem_image, Function.comp_apply] at hj
  simp only [indices, mem_union, mem_image, Function.comp_apply]
  rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨x, hx, rfl⟩
  · exact Or.inl (Or.inl ⟨i, hT hi, rfl⟩)
  · obtain ⟨hi, -, hk⟩ := (A.mem_relSel).mp hr
    exact Or.inl (Or.inr ⟨r, (A.mem_relIdx).mpr ⟨hi, hk⟩, rfl⟩)
  · exact Or.inr ⟨(x, f x), hedge x (mem_range.mp hx), rfl⟩

/-! ### Membership, multiplicities and sizes -/

theorem ids_subset_allIds {n m : ℕ} {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hHfst : ∀ h ∈ H, h.1 < n)
    (hHsnd : ∀ h ∈ H, h.2 ∈ (range m).disjSum (range A.z))
    {j : JIdx κ} (hj : j ∈ A.indices H) : A.ids j ⊆ A.allIds n m := by
  intro t ht
  simp only [indices, mem_union, mem_image, Function.comp_apply] at hj
  simp only [allIds, mem_union, mem_image, mem_range]
  rcases hj with (⟨i, hi, rfl⟩ | ⟨r, hr, rfl⟩) | ⟨h, hh, rfl⟩
  · simp only [ids, idsPar, mem_union, mem_image, mem_range] at ht
    rcases ht with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
    · exact Or.inl (Or.inl (Or.inr ⟨_, A.slot_lt (A.mem_D_false hi hk), rfl⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨(i, k), (A.mem_relIdx).mpr ⟨hi, hk⟩, rfl⟩))
  · obtain ⟨hi, hk⟩ := (A.mem_relIdx).mp hr
    simp only [ids, idsRel, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (Or.inl (Or.inl ⟨r, hr, rfl⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨_, A.slot_lt (A.mem_D_true hi hk), rfl⟩))
  · simp only [ids, idsMt, mem_insert, mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact Or.inl (Or.inr ⟨h.1, hHfst h hh, rfl⟩)
    · have := hHsnd h hh
      rcases hh2 : h.2 with y | j'
      · rw [hh2] at this
        have : y < m := by simpa using this
        exact Or.inr ⟨y, this, by simp [minusId]⟩
      · rw [hh2] at this
        have : j' < A.z := by simpa using this
        exact Or.inl (Or.inl (Or.inr ⟨j', this, by simp [minusId]⟩))

theorem card_filter_idsPar_le (t : Tok κ) :
    (A.lib.filter fun i => t ∈ A.idsPar i).card ≤ 1 := by
  refine card_le_one.mpr fun i hi i' hi' => ?_
  obtain ⟨hi1, ht1⟩ := mem_filter.mp hi
  obtain ⟨hi2, ht2⟩ := mem_filter.mp hi'
  simp only [idsPar, mem_union, mem_image, mem_range] at ht1 ht2
  rcases ht1 with ⟨k, hk, h1⟩ | ⟨k, hk, h1⟩ <;> rcases ht2 with ⟨k', hk', h2⟩ | ⟨k', hk', h2⟩
  · rw [← h2] at h1
    simp only [Tok.vm.injEq] at h1
    have := A.slot_inj (A.mem_D_false hi1 hk) (A.mem_D_false hi2 hk') h1
    simp only [Prod.mk.injEq] at this
    exact this.1
  · rw [← h2] at h1; simp at h1
  · rw [← h2] at h1; simp at h1
  · rw [← h2] at h1
    simp only [Tok.pp.injEq] at h1
    exact h1.1

theorem card_filter_idsRel_le (t : Tok κ) :
    (A.relIdx.filter fun r => t ∈ A.idsRel r).card ≤ 1 := by
  refine card_le_one.mpr fun r hr r' hr' => ?_
  obtain ⟨hr1, ht1⟩ := mem_filter.mp hr
  obtain ⟨hr2, ht2⟩ := mem_filter.mp hr'
  obtain ⟨hi, hk⟩ := (A.mem_relIdx).mp hr1
  obtain ⟨hi', hk'⟩ := (A.mem_relIdx).mp hr2
  simp only [idsRel, mem_insert, mem_singleton] at ht1 ht2
  rcases ht1 with h1 | h1 <;> rcases ht2 with h2 | h2 <;> rw [h2] at h1
  · simp only [Tok.pp.injEq] at h1
    exact Prod.ext h1.1.symm h1.2.symm
  · simp at h1
  · simp at h1
  · simp only [Tok.vm.injEq] at h1
    have := A.slot_inj (A.mem_D_true hi' hk') (A.mem_D_true hi hk) h1
    simp only [Prod.mk.injEq] at this
    exact Prod.ext this.1.symm this.2.1.symm

/-- Every token identity lies in at most `44` library pieces. -/
theorem card_filter_ids_le {H : Finset (ℕ × (ℕ ⊕ ℕ))}
    (hdx : ∀ x, (H.filter fun h => h.1 = x).card ≤ 24)
    (hdy : ∀ y, (H.filter fun h => h.2 = y).card ≤ 18) (t : Tok κ) :
    ((A.indices H).filter fun j => t ∈ A.ids j).card ≤ 44 := by
  unfold indices
  rw [filter_union, filter_union]
  refine (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
    (Nat.add_le_add ?_ ?_)) ?_) |>.trans (by norm_num : 1 + 1 + 42 ≤ 44)
  · rw [filter_image]
    exact card_image_le.trans (A.card_filter_idsPar_le t)
  · rw [filter_image]
    exact card_image_le.trans (A.card_filter_idsRel_le t)
  · rw [filter_image]
    exact card_image_le.trans (EvenRefiner.card_filter_idsMt_le hdx hdy t)

theorem card_ids_inl (i : κ) : (A.ids (Sum.inl i)).card ≤ (A.c i).natAbs := by
  simp only [ids, idsPar]
  refine (card_union_le _ _).trans ?_
  rw [← A.mc_add_pc i]
  exact Nat.add_le_add (card_image_le.trans (by simp)) (card_image_le.trans (by simp))

theorem card_ids_inr (j : (κ × ℕ) ⊕ (ℕ × (ℕ ⊕ ℕ))) : (A.ids (Sum.inr j)).card ≤ 2 := by
  rcases j with r | h
  · exact card_le_two
  · exact card_le_two

theorem card_indices_le {H : Finset (ℕ × (ℕ ⊕ ℕ))} {n : ℕ} (hfst : ∀ h ∈ H, h.1 < n)
    (hdx : ∀ x, (H.filter fun h => h.1 = x).card ≤ 24) :
    (A.indices H).card ≤ A.lib.card + A.z + 24 * n := by
  have hH := EvenRefiner.card_le_of_fst hfst hdx
  have hrel := A.card_relIdx_le
  unfold indices
  refine (card_union_le _ _).trans (Nat.add_le_add ((card_union_le _ _).trans
    (Nat.add_le_add card_image_le card_image_le)) card_image_le) |>.trans ?_
  omega

end Ledger

end PartitionedTriangleAbsorption.StructuralF3
