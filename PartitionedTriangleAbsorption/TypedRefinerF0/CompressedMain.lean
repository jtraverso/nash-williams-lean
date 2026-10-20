/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.Main
public import PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHubLoads

/-! # Typed F0 producer with compressed hubs

The height is free: M = 2^p. Whole-library hub incidence is at most
330 (|V|/M + 1) Δ + 1452 M, and the number of pieces is at most
57635 (|X| + 2 M²). All quantifiers precede the divisible leftover.
This is an abstract refiner, not a physical host embedding.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks UniversalRefiner

variable (V : Type*) [Fintype V] [DecidableEq V]

abbrev RefU (p : ℕ) := HU V p
abbrev RefW (p : ℕ) := W1 (WP (RefU V p)) (LibIdx (RefU V p))
abbrev RefI (p : ℕ) := JIdx (LibIdx (RefU V p))

instance (p : ℕ) : DecidableEq (RefW V p) := inferInstance

variable {V}

def refEmb (p : ℕ) (v : V) : RefW V p := Sum.inl (Sum.inl (Sum.inl v))

def pwMid (p : ℕ) (pV : V → Fin 2) : WP (RefU V p) → Fin 2
  | Sum.inl (Sum.inl v) => pV v
  | _ => 0

def refPart (p : ℕ) (pV : V → Fin 2) : RefW V p → Fin 2 := pw1 (pwMid p pV)

omit [Fintype V] [DecidableEq V] in
theorem refPart_refEmb (p : ℕ) (pV : V → Fin 2) (v : V) :
    refPart p pV (refEmb p v) = pV v := rfl

/-- **The typed F0 refiner producer.** -/
theorem typed_refiner_F0_compressed (p : ℕ) (pV : V → Fin 2)
    (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∃ (indices : Finset (RefI V p)) (B : RefI V p → Finset (Sym2 (RefW V p)))
      (R : Finset (Sym2 (RefW V p))),
      Disjoint R (mapE (refEmb p) X) ∧
      RefinerAssembly.RefinesReserve (p := refPart p pV) (F := F0) indices B (mapE (refEmb p) X) R ∧
      (∀ j ∈ indices, IsIntDiv (refPart p pV) F0 (B j) ∧ (∀ e ∈ B j, ¬ e.IsDiag) ∧
        (∀ w, Even (incidentLoad (B j) w)) ∧ B j ⊆ R ∪ mapE (refEmb p) X ∧ (B j).card ≤ 214) ∧
      (∀ v, ∑ j ∈ indices, incidentLoad (B j) ((refEmb p) v) ≤ 99 * incidentLoad X v) ∧
      (∀ r, ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inr r)) ≤ 66) ∧
      (∀ t a, ∑ j ∈ indices, incidentLoad (B j) (Sum.inr (t, a)) ≤ 88) ∧
      (∀ D, (∀ v, incidentLoad X v ≤ D) → ∀ i : Fin (2 ^ (p + 1)),
        ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inl (Sum.inr i))) ≤
          330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p) ∧
      indices.card ≤ 57635 * (X.card + 2 * (2 ^ p) ^ 2) := by
  set X1 : Finset (Sym2 (RefU V p)) := mapE Sum.inl X
  have hX1 : ∀ e ∈ X1, ¬ e.IsDiag := loopless_mapE Sum.inl_injective hX
  set base : RefU V p := hubOf p 0
  let E := parityRefiner (X := X1) (hmap := heapH p) (L := p + 1) base hX1
    (heap_links_last X) (heap_nofix X)
  obtain ⟨indices, R, hdisj, href, hpieces, hold, htok, hcard⟩ := E.charge_layer (pwMid p pV)
  have hlift : (liftE (κ := LibIdx (RefU V p)) (mapE Sum.inl X1) : Finset (Sym2 (RefW V p))) =
      mapE (refEmb p) X := by
    simp only [liftE, X1, mapE_mapE]; rfl
  rw [hlift] at hdisj href hpieces
  have hPcard : ∀ i, (E.P i).card ≤ 22 := fun i =>
    (card_physE_le _ _).trans (by have := card_piece_le' X1 (heapH p) i; omega)
  refine ⟨indices, E.Bt (pwMid p pV), R, hdisj, href, ?_, ?_, ?_, htok, ?_, ?_⟩
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
    rw [show ((refEmb p) v : RefW V p) = Sum.inl (Sum.inl (Sum.inl v)) from rfl, hold]
    refine (sum_evenLib_load_inl X1 (heapH p) (p + 1) base (Sum.inl v)).trans ?_
    rw [heap_root_old X v]
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
        10 * ((Fintype.card V / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) := heap_root_hub X D hD i
    have h2 : (vChain X1 (Sum.inr i)).card = 0 := by
      rw [vChain_level0_hub]; rfl
    rw [h2]
    change _ ≤ 330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p
    have hp2 := pow_succ 2 p
    omega
  · refine hcard.trans ?_
    have hlib := card_evenLib_le X1 (heapH p) (p + 1) base
    have hsum := sum_card_physE_le X1 (heapH p) (p + 1) base
    have hL := heap_sum_links_compressed (p := p) X
    have hX1c : X1.card = X.card := card_mapE Sum.inl_injective X
    change (evenLib X1 (heapH p) (p + 1) base).card + 97 * ∑ i ∈ evenLib X1 (heapH p) (p + 1) base,
      (physE (rtP (heapH p) base) (UniversalRefiner.piece X1 (heapH p) i)).card ≤ _
    rw [hX1c] at hsum
    nlinarith

end PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub


