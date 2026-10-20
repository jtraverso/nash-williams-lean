/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeLayer
public import PartitionedTriangleAbsorption.TypedRefinerF0.HubLoads

/-! # The typed F0 refiner producer

`typed_refiner_F0`: for every finite vertex type `V` with a part function `pV : V → Fin 2` and
every loopless reserve `X` on `V`, there is — before any leftover is chosen — an explicit
extension `RefW V` of the vertex type (auxiliary hubs, labelled middle vertices of requests,
and labelled token vertices), a fixed remainder `R` disjoint from the copy of `X`, and a fixed
finite library `B` of loopless, everywhere-even, integrally F0-divisible pieces such that every
integrally F0-divisible leftover `L ⊆ X` selects pairwise edge-disjoint library pieces whose
union is exactly `R ∪ L` (`RefinerAssembly.RefinesReserve`).

Quantitative control (whole library, not just the selected pieces):
* every piece has at most `214` edges;
* an original vertex `v` lies in at most `99 · deg_X(v)` library edges (counted over all
  pieces);
* every middle vertex lies in at most `66`, and every token vertex in at most `88`, library edges;
* a hub vertex lies in at most `330 Δ + 726 · 2^(pOf V + 1) ≤ 330 Δ + 2904 (|V| + 1)` library
  edges — this is **not** `O(Δ + 1)`; see `TYPED_REFINER_F0_STAGE38.md`;
* the number of pieces is at most `57635 · (log₂|V| + 2) · |X|`.

No host graph and no embedding is involved: this is the abstract refiner only.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks UniversalRefiner

variable (V : Type*) [Fintype V] [DecidableEq V]

/-- Heap height used for `V`: `|V| < 2 ^ pOf V`. -/
def pOf : ℕ := Nat.log 2 (Fintype.card V) + 1

omit [DecidableEq V] in
theorem card_lt_two_pow_pOf : Fintype.card V < 2 ^ pOf V :=
  Nat.lt_pow_succ_log_self (by norm_num) _

/-- Old vertices and hubs. -/
abbrev RefU := HU V (pOf V)

/-- The extended vertex type of the refiner. -/
abbrev RefW := W1 (WP (RefU V)) (LibIdx (RefU V))

instance : DecidableEq (RefW V) := inferInstance

/-- Library indices of the refiner. -/
abbrev RefI := JIdx (LibIdx (RefU V))

variable {V}

/-- The copy of an old vertex. -/
def refEmb (v : V) : RefW V := Sum.inl (Sum.inl (Sum.inl v))

/-- Part function on the middle layer: old vertices keep their part, the rest get part `0`. -/
def pwMid (pV : V → Fin 2) : WP (RefU V) → Fin 2
  | Sum.inl (Sum.inl v) => pV v
  | _ => 0

/-- The part function of the extended vertex type. -/
def refPart (pV : V → Fin 2) : RefW V → Fin 2 := pw1 (pwMid pV)

omit [DecidableEq V] in
theorem refPart_refEmb (pV : V → Fin 2) (v : V) : refPart pV (refEmb v) = pV v := rfl

omit [DecidableEq V] in
theorem refEmb_injective : Function.Injective (refEmb (V := V)) := by
  intro a b h; simpa [refEmb] using h

theorem mapE_mapE {α β γ : Type*} [DecidableEq β] [DecidableEq γ] (f : β → γ) (g : α → β)
    (E : Finset (Sym2 α)) : mapE f (mapE g E) = mapE (f ∘ g) E := by
  simp only [mapE, image_image, Sym2.map_comp]

omit [DecidableEq V] in
theorem two_pow_pOf_le : 2 ^ (pOf V + 1) ≤ 4 * Fintype.card V + 4 := by
  unfold pOf
  rcases Nat.eq_zero_or_pos (Fintype.card V) with h | h
  · rw [h]; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h)
    rw [pow_succ, pow_succ]
    omega

omit [Fintype V] in
theorem card_piece_le' (X : Finset (Sym2 V)) (hmap : ℕ → V → V) (i : LibIdx V) :
    (UniversalRefiner.piece X hmap i).card ≤ 11 := by
  cases i with
  | alt l π x ca cb cs =>
    exact card_altAtoms_le (Λ := links X hmap l) (h := hmap l) (l := l) π x ca cb cs
  | cyc l σ => exact card_le_two.trans (by norm_num)
  | adj k => exact card_le_two.trans (by norm_num)

/-- **The typed F0 refiner producer.** -/
theorem typed_refiner_F0 (pV : V → Fin 2) (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∃ (indices : Finset (RefI V)) (B : RefI V → Finset (Sym2 (RefW V)))
      (R : Finset (Sym2 (RefW V))),
      Disjoint R (mapE refEmb X) ∧
      RefinerAssembly.RefinesReserve (p := refPart pV) (F := F0) indices B (mapE refEmb X) R ∧
      (∀ j ∈ indices, IsIntDiv (refPart pV) F0 (B j) ∧ (∀ e ∈ B j, ¬ e.IsDiag) ∧
        (∀ w, Even (incidentLoad (B j) w)) ∧ B j ⊆ R ∪ mapE refEmb X ∧ (B j).card ≤ 214) ∧
      (∀ v, ∑ j ∈ indices, incidentLoad (B j) (refEmb v) ≤ 99 * incidentLoad X v) ∧
      (∀ r, ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inr r)) ≤ 66) ∧
      (∀ t a, ∑ j ∈ indices, incidentLoad (B j) (Sum.inr (t, a)) ≤ 88) ∧
      (∀ D, (∀ v, incidentLoad X v ≤ D) → ∀ i : Fin (2 ^ (pOf V + 1)),
        ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inl (Sum.inr i))) ≤
          330 * D + 726 * 2 ^ (pOf V + 1)) ∧
      indices.card ≤ 57635 * (pOf V + 1) * X.card := by
  set p := pOf V
  have hp : Fintype.card V < 2 ^ p := card_lt_two_pow_pOf V
  set X1 : Finset (Sym2 (RefU V)) := mapE Sum.inl X
  have hX1 : ∀ e ∈ X1, ¬ e.IsDiag := loopless_mapE Sum.inl_injective hX
  set base : RefU V := hubOf p 0
  let E := parityRefiner (X := X1) (hmap := heapH p) (L := p + 1) base hX1
    (heap_links_last X hp) (heap_nofix X hp)
  obtain ⟨indices, R, hdisj, href, hpieces, hold, htok, hcard⟩ := E.charge_layer (pwMid pV)
  have hlift : (liftE (κ := LibIdx (RefU V)) (mapE Sum.inl X1) : Finset (Sym2 (RefW V))) =
      mapE refEmb X := by
    simp only [liftE, X1, mapE_mapE]; rfl
  rw [hlift] at hdisj href hpieces
  have hPcard : ∀ i, (E.P i).card ≤ 22 := fun i =>
    (card_physE_le _ _).trans (by have := card_piece_le' X1 (heapH p) i; omega)
  refine ⟨indices, E.Bt (pwMid pV), R, hdisj, href, ?_, ?_, ?_, htok, ?_, ?_⟩
  · intro j hj
    obtain ⟨hdiv, hloop, hsub, hc⟩ := hpieces j hj
    refine ⟨hdiv, hloop, fun w => TypedDivisibilityCollapse.even_of_isIntDiv
      TypedTransportExamples.F0_card hloop hdiv w, hsub, hc.trans ?_⟩
    have : (E.oldPart j).card ≤ 22 := by
      rcases j with i | j
      · exact hPcard i
      · simp [EvenRefiner.oldPart]
    omega
  · intro v
    rw [show (refEmb v : RefW V) = Sum.inl (Sum.inl (Sum.inl v)) from rfl, hold]
    refine (sum_evenLib_load_inl X1 (heapH p) (p + 1) base (Sum.inl v)).trans ?_
    rw [heap_root_old X hp v]
    have h1 : (vChain X1 (Sum.inl v)).card = incidentLoad X v :=
      incidentLoad_mapE_apply Sum.inl_injective X v
    rw [h1]
    omega
  · intro r
    rw [hold]
    exact sum_evenLib_load_inr X1 (heapH p) (p + 1) base r
  · intro D hD i
    rw [hold]
    refine (sum_evenLib_load_inl X1 (heapH p) (p + 1) base (Sum.inr i)).trans ?_
    have h1 : ∑ l ∈ range (p + 1), (2 * (vChain (links X1 (heapH p) l) (Sum.inr i)).card +
        10 * hubWeight (links X1 (heapH p) l) (heapH p l) (Sum.inr i)) ≤
        10 * D + 22 * 2 ^ (p + 1) := heap_root_hub X hp D hD i
    have h2 : (vChain X1 (Sum.inr i)).card = 0 := by
      rw [vChain_level0_hub]; rfl
    rw [h2]
    change _ ≤ 330 * D + 726 * 2 ^ (p + 1)
    omega
  · refine hcard.trans ?_
    have hlib := card_evenLib_le X1 (heapH p) (p + 1) base
    have hsum := sum_card_physE_le X1 (heapH p) (p + 1) base
    have hL := heap_sum_links_le X (heapH p) (p + 1)
    have hX1c : X1.card = X.card := card_mapE Sum.inl_injective X
    change (evenLib X1 (heapH p) (p + 1) base).card + 97 * ∑ i ∈ evenLib X1 (heapH p) (p + 1) base,
      (physE (rtP (heapH p) base) (UniversalRefiner.piece X1 (heapH p) i)).card ≤ _
    rw [hX1c] at hsum
    nlinarith

end PartitionedTriangleAbsorption.TypedRefinerF0
