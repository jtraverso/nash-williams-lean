/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.TokenPieces
public import PartitionedTriangleAbsorption.TypedRefinerF0.RobustSlots

/-! # The charge layer: definitions

Input: an *even refiner* (`EvenRefiner`): a fixed remainder `R0` and a library of loopless
even pieces `P i` such that every even `L ⊆ X0` is exactly partitioned, together with `R0`,
by pairwise disjoint pieces. Pieces need not have zero charge.

Every piece `i` gets `c i = charge(P i)/4` charge tokens of the opposite sign
(`mc i` minus tokens if `c i > 0`, `pc i` plus tokens if `c i < 0`). A plus token `pp i k` of
a negative piece has a *release* piece `{pp i k, twin}` with a minus twin. All minus tokens
that may be left uncovered (the minus tokens of positive pieces and the twins) are the
*variable slots* `vm j`, `j < z`, enumerated through `D`. Fixed buffers `bp x` (plus) and
`bm y` (minus) and a robust graph `H` (`exists_robust`) supply the *matching pieces*
`{bp x, minus y}`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge

variable {W0 : Type*} [DecidableEq W0] {κ : Type*} [DecidableEq κ]

/-- An even (parity-only) refiner of the reserve `X0`. -/
structure EvenRefiner (κ : Type*) (X0 : Finset (Sym2 W0)) where
  lib : Finset κ
  P : κ → Finset (Sym2 W0)
  R0 : Finset (Sym2 W0)
  loopP : ∀ i ∈ lib, ∀ e ∈ P i, ¬ e.IsDiag
  evenP : ∀ i ∈ lib, ∀ w, Even (incidentLoad (P i) w)
  subP : ∀ i ∈ lib, P i ⊆ R0 ∪ X0
  loopX : ∀ e ∈ X0, ¬ e.IsDiag
  disjRX : Disjoint R0 X0
  refines : ∀ L ⊆ X0, (∀ w, Even (incidentLoad L w)) →
    ∃ T ⊆ lib, (T : Set κ).PairwiseDisjoint P ∧ T.biUnion P = R0 ∪ L

namespace EvenRefiner

variable {X0 : Finset (Sym2 W0)} (pw0 : W0 → Fin 2) (E : EvenRefiner κ X0)

/-- Quarter charge of a piece. -/
noncomputable def chg (i : κ) : ℤ := charge chi0 pw0 (E.P i) / 4

/-- Number of minus tokens attached to piece `i`. -/
noncomputable def mc (i : κ) : ℕ := (E.chg pw0 i).toNat

/-- Number of plus tokens attached to piece `i`. -/
noncomputable def pc (i : κ) : ℕ := (-E.chg pw0 i).toNat

/-- Descriptors of the variable minus tokens contributed by piece `i`:
`(i,k,false)` its own minus tokens, `(i,k,true)` the twins of its plus tokens. -/
noncomputable def descOf (i : κ) : Finset (κ × ℕ × Bool) :=
  (range (E.mc pw0 i)).image (fun k => (i, k, false)) ∪
    (range (E.pc pw0 i)).image (fun k => (i, k, true))

/-- All variable descriptors. -/
noncomputable def D : Finset (κ × ℕ × Bool) := E.lib.biUnion (E.descOf pw0)

/-- The slot of a descriptor. -/
noncomputable def slot (d : κ × ℕ × Bool) : ℕ := UniversalRefiner.pos (E.D pw0) d

/-- Number of variable slots. -/
noncomputable def z : ℕ := (E.D pw0).card

/-- The number of present variable slots, the same for every leftover. -/
noncomputable def sNum : ℕ :=
  ((∑ i ∈ E.lib, (E.mc pw0 i : ℤ)) - charge chi0 pw0 E.R0 / 4).toNat

/-- Token identities of the parity piece `i`. -/
noncomputable def idsPar (i : κ) : Finset (Tok κ) :=
  (range (E.mc pw0 i)).image (fun k => Tok.vm (E.slot pw0 (i, k, false))) ∪
    (range (E.pc pw0 i)).image (fun k => Tok.pp i k)

/-- Token identities of the release piece of `pp i k`. -/
noncomputable def idsRel (r : κ × ℕ) : Finset (Tok κ) :=
  {Tok.pp r.1 r.2, Tok.vm (E.slot pw0 (r.1, r.2, true))}

end EvenRefiner

/-- The token of a minus vertex of the robust graph. -/
def minusId : ℕ ⊕ ℕ → Tok κ
  | Sum.inl y => Tok.bm y
  | Sum.inr j => Tok.vm j

omit [DecidableEq κ] in
theorem minusId_injective : Function.Injective (minusId (κ := κ)) := by
  rintro (a | a) (b | b) h <;> simp_all [minusId]

/-- Token identities of a matching piece. -/
def idsMt (h : ℕ × (ℕ ⊕ ℕ)) : Finset (Tok κ) := {Tok.bp h.1, minusId h.2}

/-- Library indices: parity pieces, release pieces, matching pieces. -/
abbrev JIdx (κ : Type*) := κ ⊕ (κ × ℕ) ⊕ (ℕ × (ℕ ⊕ ℕ))

namespace EvenRefiner

variable {X0 : Finset (Sym2 W0)} (pw0 : W0 → Fin 2) (E : EvenRefiner κ X0)

/-- Token identities of a library index. -/
noncomputable def ids : JIdx κ → Finset (Tok κ)
  | Sum.inl i => E.idsPar pw0 i
  | Sum.inr (Sum.inl r) => E.idsRel pw0 r
  | Sum.inr (Sum.inr h) => idsMt h

/-- Old edges of a library index. -/
def oldPart : JIdx κ → Finset (Sym2 W0)
  | Sum.inl i => E.P i
  | Sum.inr _ => ∅

/-- **The typed pieces.** -/
noncomputable def Bt (j : JIdx κ) : Finset (Sym2 (W1 W0 κ)) := piece (E.oldPart j) (E.ids pw0 j)

/-- Release indices. -/
noncomputable def relIdx : Finset (κ × ℕ) :=
  E.lib.biUnion fun i => (range (E.pc pw0 i)).image fun k => (i, k)

/-- The library for a robust graph `H`. -/
noncomputable def indices (H : Finset (ℕ × (ℕ ⊕ ℕ))) : Finset (JIdx κ) :=
  E.lib.image Sum.inl ∪ (E.relIdx pw0).image (Sum.inr ∘ Sum.inl) ∪ H.image (Sum.inr ∘ Sum.inr)

/-- All token identities of the remainder. -/
noncomputable def allIds (m : ℕ) : Finset (Tok κ) :=
  (E.relIdx pw0).image (fun r => Tok.pp r.1 r.2) ∪ (range (E.z pw0)).image Tok.vm ∪
    (range (m + E.sNum pw0)).image Tok.bp ∪ (range m).image Tok.bm

/-- **The typed remainder.** -/
noncomputable def Rt (m : ℕ) : Finset (Sym2 (W1 W0 κ)) := piece E.R0 (E.allIds pw0 m)

/-! ### Basic facts -/

theorem mem_D {d : κ × ℕ × Bool} :
    d ∈ E.D pw0 ↔ d.1 ∈ E.lib ∧ ((d.2.2 = false ∧ d.2.1 < E.mc pw0 d.1) ∨
      (d.2.2 = true ∧ d.2.1 < E.pc pw0 d.1)) := by
  rcases d with ⟨i, k, b⟩
  simp only [D, descOf, mem_biUnion, mem_union, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', (⟨k', hk', rfl, rfl, rfl⟩ | ⟨k', hk', rfl, rfl, rfl⟩)⟩
    · exact ⟨hi', Or.inl ⟨rfl, hk'⟩⟩
    · exact ⟨hi', Or.inr ⟨rfl, hk'⟩⟩
  · rintro ⟨hi, (⟨rfl, hk⟩ | ⟨rfl, hk⟩)⟩
    · exact ⟨i, hi, Or.inl ⟨k, hk, rfl, rfl, rfl⟩⟩
    · exact ⟨i, hi, Or.inr ⟨k, hk, rfl, rfl, rfl⟩⟩

theorem mem_D_false {i : κ} {k : ℕ} (hi : i ∈ E.lib) (hk : k < E.mc pw0 i) :
    (i, k, false) ∈ E.D pw0 := by
  unfold D
  exact mem_biUnion.mpr ⟨i, hi, mem_union_left _ (mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩)⟩

theorem mem_D_true {i : κ} {k : ℕ} (hi : i ∈ E.lib) (hk : k < E.pc pw0 i) :
    (i, k, true) ∈ E.D pw0 := by
  unfold D
  exact mem_biUnion.mpr ⟨i, hi, mem_union_right _ (mem_image.mpr ⟨k, mem_range.mpr hk, rfl⟩)⟩

theorem slot_inj {d d' : κ × ℕ × Bool} (hd : d ∈ E.D pw0) (hd' : d' ∈ E.D pw0)
    (h : E.slot pw0 d = E.slot pw0 d') : d = d' :=
  UniversalRefiner.pos_inj hd hd' h

theorem slot_lt {d : κ × ℕ × Bool} (hd : d ∈ E.D pw0) : E.slot pw0 d < E.z pw0 :=
  UniversalRefiner.pos_lt hd

theorem mem_relIdx {r : κ × ℕ} : r ∈ E.relIdx pw0 ↔ r.1 ∈ E.lib ∧ r.2 < E.pc pw0 r.1 := by
  rcases r with ⟨i, k⟩
  simp only [relIdx, mem_biUnion, mem_image, mem_range, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi', k', hk', rfl, rfl⟩; exact ⟨hi', hk'⟩
  · rintro ⟨hi, hk⟩; exact ⟨i, hi, k, hk, rfl, rfl⟩

omit [DecidableEq κ] in
theorem chg_eq (i : κ) : E.chg pw0 i = (E.mc pw0 i : ℤ) - E.pc pw0 i :=
  (Int.toNat_sub_toNat_neg _).symm

omit [DecidableEq κ] in
theorem charge_eq_four_chg {i : κ} (hi : i ∈ E.lib) :
    charge chi0 pw0 (E.P i) = 4 * E.chg pw0 i := by
  have h := four_dvd_charge pw0 (E.loopP i hi) (E.evenP i hi)
  unfold chg
  exact (Int.mul_ediv_cancel' h).symm

omit [DecidableEq κ] in
theorem abs_chg_le (i : κ) : |E.chg pw0 i| ≤ (E.P i).card := by
  have h := abs_charge_le (χ := chi0) (M := 4) pw0 (fun e => by
    have := abs_pair_pairVec_le (χ := chi0) (m := 2)
      (fun a b => by fin_cases a <;> fin_cases b <;> simp [chi0]) pw0 e
    linarith) (E.P i)
  unfold chg
  rw [abs_le] at h ⊢
  constructor
  · have := Int.le_ediv_of_mul_le (by norm_num : (0 : ℤ) < 4)
      (show -(E.P i).card * 4 ≤ charge chi0 pw0 (E.P i) by linarith)
    simpa using this
  · exact Int.ediv_le_of_le_mul (by norm_num) (by linarith)

omit [DecidableEq κ] in
theorem mc_add_pc_le (i : κ) : E.mc pw0 i + E.pc pw0 i ≤ (E.P i).card := by
  have h := abs_le.mp (E.abs_chg_le pw0 i)
  unfold mc pc
  omega

theorem card_descOf (i : κ) : (E.descOf pw0 i).card = E.mc pw0 i + E.pc pw0 i := by
  unfold descOf
  rw [card_union_of_disjoint]
  · rw [card_image_of_injective _ (fun a b h => by simpa using h),
      card_image_of_injective _ (fun a b h => by simpa using h), card_range, card_range]
  · rw [disjoint_left]
    intro d h1 h2
    obtain ⟨k, -, rfl⟩ := mem_image.mp h1
    obtain ⟨k', -, h⟩ := mem_image.mp h2
    simp at h

theorem z_eq : E.z pw0 = ∑ i ∈ E.lib, (E.mc pw0 i + E.pc pw0 i) := by
  unfold z D
  rw [card_biUnion]
  · exact sum_congr rfl fun i _ => E.card_descOf pw0 i
  · intro i _ i' _ hii'
    rw [Function.onFun, disjoint_left]
    intro d h1 h2
    simp only [descOf, mem_union, mem_image] at h1 h2
    rcases h1 with ⟨k, -, rfl⟩ | ⟨k, -, rfl⟩ <;>
      rcases h2 with ⟨k', -, h⟩ | ⟨k', -, h⟩ <;> simp_all

theorem z_le : E.z pw0 ≤ ∑ i ∈ E.lib, (E.P i).card := by
  rw [z_eq]; exact sum_le_sum fun i _ => E.mc_add_pc_le pw0 i

theorem card_relIdx : (E.relIdx pw0).card = ∑ i ∈ E.lib, E.pc pw0 i := by
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

/-! ### Charges of the pieces -/

theorem sum_tokCharge_idsPar {i : κ} (hi : i ∈ E.lib) :
    ∑ t ∈ E.idsPar pw0 i, tokCharge t = -4 * E.mc pw0 i + 4 * E.pc pw0 i := by
  unfold idsPar
  rw [sum_union]
  · rw [sum_image, sum_image]
    · simp [tokCharge, Tok.sign]; ring
    · intro a _ b _ h; simpa using h
    · intro a ha b hb h
      simp only [Tok.vm.injEq] at h
      have := E.slot_inj pw0 (E.mem_D_false pw0 hi (mem_range.mp ha))
        (E.mem_D_false pw0 hi (mem_range.mp hb)) h
      simpa using this
  · rw [disjoint_left]
    intro t h1 h2
    obtain ⟨k, -, rfl⟩ := mem_image.mp h1
    obtain ⟨k', -, h⟩ := mem_image.mp h2
    simp at h

theorem charge_par_zero {i : κ} (hi : i ∈ E.lib) :
    charge chi0 pw0 (E.P i) + ∑ t ∈ E.idsPar pw0 i, tokCharge t = 0 := by
  rw [E.sum_tokCharge_idsPar pw0 hi, E.charge_eq_four_chg pw0 hi, E.chg_eq pw0]
  ring

theorem charge_rel_zero (r : κ × ℕ) :
    charge chi0 pw0 (∅ : Finset (Sym2 W0)) + ∑ t ∈ E.idsRel pw0 r, tokCharge t = 0 := by
  unfold idsRel
  rw [sum_pair (by simp), charge_empty]
  simp [tokCharge, Tok.sign]

omit [DecidableEq W0] in
theorem charge_mt_zero (h : ℕ × (ℕ ⊕ ℕ)) :
    charge chi0 pw0 (∅ : Finset (Sym2 W0)) + ∑ t ∈ (idsMt h : Finset (Tok κ)), tokCharge t = 0 := by
  unfold idsMt
  rcases h with ⟨x, y | y⟩ <;>
  · rw [sum_pair (by simp [minusId]), charge_empty]
    simp [tokCharge, Tok.sign, minusId]

end EvenRefiner

end PartitionedTriangleAbsorption.TypedRefinerF0
