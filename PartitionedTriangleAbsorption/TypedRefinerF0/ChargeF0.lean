/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPieceConditions
public import PartitionedTriangleAbsorption.TypedRefinerCharge
public import PartitionedTriangleAbsorption.UniversalRefiner.Basic

/-! # The F0 charge, embeddings and charge tokens

* `edge_charge`: an edge between equal parts has charge `-4`, a crossing edge `+2`
  (`charge = pair chi0 ∘ edgeVec`, i.e. twice `e₀₁ - 2e₀₀ - 2e₁₁`);
* `four_dvd_charge`: every loopless even edge set has charge divisible by `4`;
* `isIntDiv_of_charge`: a loopless even edge set of charge `0` is integrally
  F0-divisible (`TypedPieceConditions.F0_isIntDiv_iff`);
* transport of loads, looplessness and charge along injective vertex maps;
* the two charge tokens on `Fin 8`: a `4`-cycle of charge `-4` and an `8`-cycle of charge
  `+4`, both even at every vertex.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks

/-! ### The F0 charge -/

section Charge

variable {W : Type*} [DecidableEq W]

omit [DecidableEq W] in
theorem edge_charge (pw : W → Fin 2) {a b : W} :
    pair chi0 (pairVec pw s(a, b)) = if pw a = pw b then -4 else 2 := by
  rw [pair_pairVec]
  generalize pw a = x
  generalize pw b = y
  fin_cases x <;> fin_cases y <;> simp [chi0]

omit [DecidableEq W] in
theorem edgeVec_symm' (pw : W → Fin 2) (E : Finset (Sym2 W)) (i j : Fin 2) :
    edgeVec pw E i j = edgeVec pw E j i := by
  simp only [edgeVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    rw [add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl

omit [DecidableEq W] in
theorem even_edgeVec_diag (pw : W → Fin 2) (E : Finset (Sym2 W)) (i : Fin 2) :
    Even (edgeVec pw E i i) := by
  simp only [edgeVec, Finset.sum_apply]
  refine Finset.even_sum _ fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    by_cases h : pw a = i ∧ pw b = i
    · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩]; exact ⟨1, rfl⟩
    · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩)]; exact ⟨0, rfl⟩

omit [DecidableEq W] in
theorem charge_chi0_eq (pw : W → Fin 2) (E : Finset (Sym2 W)) :
    charge chi0 pw E = -2 * edgeVec pw E 0 0 + edgeVec pw E 0 1 + edgeVec pw E 1 0 -
      2 * edgeVec pw E 1 1 := by
  simp only [charge, pair, Fin.sum_univ_two, chi0]
  simp; ring

/-- **Charge zero gives F0-divisibility** (for loopless even edge sets). -/
theorem isIntDiv_of_charge (pw : W → Fin 2) {E : Finset (Sym2 W)} (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) (hq : charge chi0 pw E = 0) :
    IsIntDiv pw F0 E := by
  rw [TypedPieceConditions.F0_isIntDiv_iff hloop]
  refine ⟨?_, heven, ?_⟩
  · intro a b _
    have : ∀ r x : Fin 2, ∃ c, ({r, x, c} : Multiset (Fin 2)) ∈ F0 := by decide
    exact this (pw a) (pw b)
  · obtain ⟨a, ha⟩ := even_edgeVec_diag pw E 0
    obtain ⟨b, hb⟩ := even_edgeVec_diag pw E 1
    have hs := edgeVec_symm' pw E 0 1
    rw [charge_chi0_eq] at hq
    refine ⟨fun τ => if τ = {0, 0, 1} then a else b, ?_⟩
    have hne : ({0, 0, 1} : Multiset (Fin 2)) ≠ {0, 1, 1} := by decide
    funext i j
    simp only [F0]
    rw [sum_pair hne]
    simp only [ite_eq_right hne.symm, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [typeEdgeVec] <;> omega

/-- The vertices touched by an edge set. -/
noncomputable def touched (E : Finset (Sym2 W)) : Finset W :=
  E.image UniversalRefiner.endA ∪ E.image UniversalRefiner.endB

theorem mem_touched {E : Finset (Sym2 W)} {e : Sym2 W} (he : e ∈ E) {v : W} (hv : v ∈ e) :
    v ∈ touched E := by
  rcases UniversalRefiner.mem_iff_endA_endB.mp hv with rfl | rfl
  · exact mem_union_left _ (mem_image_of_mem _ he)
  · exact mem_union_right _ (mem_image_of_mem _ he)

/-- **Even loopless edge sets have charge divisible by `4`.** -/
theorem four_dvd_charge (pw : W → Fin 2) {E : Finset (Sym2 W)} (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) : (4 : ℤ) ∣ charge chi0 pw E := by
  set S0 := (touched E).filter fun v => pw v = 0
  let n0 : Sym2 W → ℕ := fun e => (S0.filter fun v => v ∈ e).card
  have hswap : ∑ e ∈ E, n0 e = ∑ v ∈ S0, incidentLoad E v := by
    simp only [n0, incidentLoad, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have hedge : ∀ e ∈ E, (4 : ℤ) ∣ pair chi0 (pairVec pw e) - 2 * (n0 e : ℤ) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := fun h => hloop _ he (by simp [h])
      have hfa : a ∈ touched E := mem_touched he (Sym2.mem_mk_left a b)
      have hfb : b ∈ touched E := mem_touched he (Sym2.mem_mk_right a b)
      have hn : S0.filter (fun v => v ∈ s(a, b)) =
          ({a, b} : Finset W).filter (fun v => pw v = 0) := by
        ext v
        simp only [S0, mem_filter, Sym2.mem_iff, mem_insert, mem_singleton]
        constructor
        · rintro ⟨⟨-, h0⟩, h⟩; exact ⟨h, h0⟩
        · rintro ⟨h, h0⟩
          rcases h with rfl | rfl
          · exact ⟨⟨hfa, h0⟩, Or.inl rfl⟩
          · exact ⟨⟨hfb, h0⟩, Or.inr rfl⟩
      simp only [n0]
      rw [hn, edge_charge, filter_insert, filter_singleton]
      generalize pw a = x at *
      generalize pw b = y at *
      fin_cases x <;> fin_cases y <;> simp [hab]
  have h1 : (4 : ℤ) ∣ charge chi0 pw E - 2 * ∑ e ∈ E, (n0 e : ℤ) := by
    rw [charge_eq_sum, mul_sum, ← sum_sub_distrib]
    exact dvd_sum hedge
  have h2 : (4 : ℤ) ∣ 2 * ∑ e ∈ E, (n0 e : ℤ) := by
    have : ∑ e ∈ E, (n0 e : ℤ) = ((∑ v ∈ S0, incidentLoad E v : ℕ) : ℤ) := by
      rw [← hswap]; push_cast; rfl
    rw [this]
    have hev : Even (∑ v ∈ S0, incidentLoad E v) := even_sum _ fun v _ => heven v
    obtain ⟨r, hr⟩ := hev
    rw [hr]; push_cast
    exact ⟨r, by ring⟩
  have := dvd_add h1 h2
  simpa using this

end Charge

/-! ### Injective vertex maps -/

section Embedding

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- Transport of an edge set along a vertex map. -/
def mapE (ι : α → β) (E : Finset (Sym2 α)) : Finset (Sym2 β) := E.image (Sym2.map ι)

omit [DecidableEq α] in
theorem mem_mapE {ι : α → β} {E : Finset (Sym2 α)} {e : Sym2 β} :
    e ∈ mapE ι E ↔ ∃ e' ∈ E, Sym2.map ι e' = e := by
  simp [mapE]

theorem mapE_union (ι : α → β) (A B : Finset (Sym2 α)) :
    mapE ι (A ∪ B) = mapE ι A ∪ mapE ι B := image_union _ _

theorem mapE_biUnion {κ : Type*} (ι : α → β) (s : Finset κ) (A : κ → Finset (Sym2 α)) :
    mapE ι (s.biUnion A) = s.biUnion fun i => mapE ι (A i) := by
  ext; simp only [mapE, mem_image, mem_biUnion]; aesop

omit [DecidableEq α] in
theorem card_mapE {ι : α → β} (hι : Function.Injective ι) (E : Finset (Sym2 α)) :
    (mapE ι E).card = E.card := card_image_of_injective _ (Sym2.map.injective hι)

omit [DecidableEq α] in
theorem disjoint_mapE {ι : α → β} (hι : Function.Injective ι) {A B : Finset (Sym2 α)}
    (h : Disjoint A B) : Disjoint (mapE ι A) (mapE ι B) := by
  unfold mapE
  exact (disjoint_image (Sym2.map.injective hι)).mpr h

omit [DecidableEq α] in
theorem loopless_mapE {ι : α → β} (hι : Function.Injective ι) {E : Finset (Sym2 α)}
    (h : ∀ e ∈ E, ¬ e.IsDiag) : ∀ e ∈ mapE ι E, ¬ e.IsDiag := by
  intro e he
  obtain ⟨e', he', rfl⟩ := mem_mapE.mp he
  rw [Sym2.isDiag_map hι]
  exact h e' he'

theorem incidentLoad_mapE_apply {ι : α → β} (hι : Function.Injective ι) (E : Finset (Sym2 α))
    (a : α) : incidentLoad (mapE ι E) (ι a) = incidentLoad E a := by
  unfold incidentLoad mapE
  rw [filter_image]
  have : (E.filter fun e => ι a ∈ Sym2.map ι e) = E.filter fun e => a ∈ e := by
    refine filter_congr fun e _ => ?_
    rw [Sym2.mem_map]
    constructor
    · rintro ⟨b, hb, hab⟩; rwa [← hι hab]
    · intro h; exact ⟨a, h, rfl⟩
  rw [this, card_image_of_injective _ (Sym2.map.injective hι)]

omit [DecidableEq α] in
theorem incidentLoad_mapE_of_not_mem {ι : α → β} (E : Finset (Sym2 α)) {b : β}
    (hb : ∀ a, ι a ≠ b) : incidentLoad (mapE ι E) b = 0 := by
  unfold incidentLoad
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hbe
  obtain ⟨e', -, rfl⟩ := mem_mapE.mp he
  obtain ⟨a, -, rfl⟩ := Sym2.mem_map.mp hbe
  exact hb a rfl

omit [DecidableEq α] [DecidableEq β] in
theorem pairVec_map (pw : β → Fin 2) (ι : α → β) (e : Sym2 α) :
    pairVec pw (Sym2.map ι e) = pairVec (pw ∘ ι) e := by
  induction e using Sym2.ind with
  | _ a b => simp [pairVec]

omit [DecidableEq α] in
theorem charge_mapE (pw : β → Fin 2) {ι : α → β} (hι : Function.Injective ι)
    (E : Finset (Sym2 α)) : charge chi0 pw (mapE ι E) = charge chi0 (pw ∘ ι) E := by
  rw [charge_eq_sum, charge_eq_sum, mapE, sum_image (fun x _ y _ h => Sym2.map.injective hι h)]
  simp only [pairVec_map]

end Embedding

/-! ### Charge tokens -/

/-- The minus token: a `4`-cycle on parts `0,0,1,1`. -/
def minusG : Finset (Sym2 (Fin 8)) := {s(0, 1), s(1, 2), s(2, 3), s(3, 0)}

/-- The plus token: an `8`-cycle on parts `0,1,0,1,1,0,0,1`. -/
def plusG : Finset (Sym2 (Fin 8)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 6), s(6, 7), s(7, 0)}

def minusPart : Fin 8 → Fin 2 := ![0, 0, 1, 1, 0, 0, 0, 0]

def plusPart : Fin 8 → Fin 2 := ![0, 1, 0, 1, 1, 0, 0, 1]

/-- The token of a given sign (`true` = plus). -/
def gadget (b : Bool) : Finset (Sym2 (Fin 8)) := if b then plusG else minusG

def gadgetPart (b : Bool) : Fin 8 → Fin 2 := if b then plusPart else minusPart

theorem gadget_loopless (b : Bool) : ∀ e ∈ gadget b, ¬ e.IsDiag := by
  cases b <;> decide

theorem gadget_even (b : Bool) : ∀ j, Even (incidentLoad (gadget b) j) := by
  cases b <;> unfold incidentLoad <;> decide

theorem gadget_card_le (b : Bool) : (gadget b).card ≤ 8 := by
  cases b <;> decide

theorem gadget_charge (b : Bool) :
    charge chi0 (gadgetPart b) (gadget b) = if b then 4 else -4 := by
  cases b
  · simp only [gadget, gadgetPart, minusG, Bool.false_eq_true, ite_false]
    rw [charge_eq_sum]
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
    simp only [edge_charge]
    decide
  · simp only [gadget, gadgetPart, plusG, ite_true]
    rw [charge_eq_sum]
    rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
      sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
      sum_insert (by decide), sum_singleton]
    simp only [edge_charge]
    decide

theorem gadget_incidentLoad_le (b : Bool) (j : Fin 8) : incidentLoad (gadget b) j ≤ 2 := by
  revert j
  cases b <;> unfold incidentLoad <;> decide

end PartitionedTriangleAbsorption.TypedRefinerF0
