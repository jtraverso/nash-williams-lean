/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRefinerF0.CompressedMain
public import PartitionedTriangleAbsorption.F0RequestLabels
public import PartitionedTriangleAbsorption.F0PatternSupply

/-! # The compressed F0 producer with arbitrary pre-correction labels

The parity hierarchy is unchanged. Charge correction is rebuilt for the given
labels, preserving all uniform library bounds. This does not relabel an already
corrected library, and does not produce a physical shared embedding.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0FlexibleCompressed

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks UniversalRefiner
open TypedRefinerF0 hiding heapH hubOf
open TypedRefinerF0.CompressedHub

variable {V : Type*} [Fintype V] [DecidableEq V]

def hubPart (p : ℕ) (pV : V → Fin 2) : RefU V p → Fin 2
  | Sum.inl v => pV v
  | Sum.inr _ => 0

noncomputable def compatibleMid (p : ℕ) (pV : V → Fin 2) : WP (RefU V p) → Fin 2
  | Sum.inl u => hubPart p pV u
  | Sum.inr r => F0RequestLabels.centrePart
      (hubPart p pV (rtP (heapH p) (hubOf p 0) r).1)
      (hubPart p pV (rtP (heapH p) (hubOf p 0) r).2)

noncomputable def compatiblePart (p : ℕ) (pV : V → Fin 2) : RefW V p → Fin 2 :=
  pw1 (compatibleMid p pV)

omit [DecidableEq V] in
theorem compatible_roots (p : ℕ) (pV : V → Fin 2) (v : V) :
    compatiblePart p pV (refEmb p v) = pV v := rfl

omit [DecidableEq V] in
theorem compatible_request (p : ℕ) (pV : V → Fin 2) (r : Req (RefU V p)) :
    ({compatibleMid p pV (Sum.inl (rtP (heapH p) (hubOf p 0) r).1),
      compatibleMid p pV (Sum.inl (rtP (heapH p) (hubOf p 0) r).2),
      compatibleMid p pV (Sum.inr r)} : Multiset (Fin 2)) ∈ F0 :=
  F0RequestLabels.centre_permitted _ _

noncomputable def requestEndpoints (p : ℕ) (r : Req (RefU V p)) :
    RefW V p × RefW V p :=
  (Sum.inl (Sum.inl (rtP (heapH p) (hubOf p 0) r).1),
    Sum.inl (Sum.inl (rtP (heapH p) (hubOf p 0) r).2))

/-- Supply for the actual request query; only the two already placed labels are used. -/
theorem request_host_supply (p : ℕ) (pV : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (alpha : ℝ) (hanti : AntiEdgeful pV F0 G alpha)
    (r : Req (RefU V p)) (f : RefW V p → V)
    (ha : pV (f (requestEndpoints p r).1) = compatiblePart p pV (requestEndpoints p r).1)
    (hb : pV (f (requestEndpoints p r).2) = compatiblePart p pV (requestEndpoints p r).2)
    (hne : f (requestEndpoints p r).1 ≠ f (requestEndpoints p r).2) :
    alpha * Fintype.card V ≤
      (TypedEmbeddingSelection.typedNeighbours pV G
        {f (requestEndpoints p r).1, f (requestEndpoints p r).2}
        (compatiblePart p pV (Sum.inl (Sum.inr r)))).card := by
  apply F0PatternSupply.pair_supply pV G alpha hanti _ _ hne
  rw [ha, hb]
  exact compatible_request p pV r

theorem flexible_producer (p : ℕ) (label : WP (RefU V p) → Fin 2)
    (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∃ (indices : Finset (RefI V p)) (B : RefI V p → Finset (Sym2 (RefW V p)))
      (R : Finset (Sym2 (RefW V p))),
      Disjoint R (mapE (refEmb p) X) ∧
      RefinerAssembly.RefinesReserve (p := pw1 label) (F := F0)
        indices B (mapE (refEmb p) X) R ∧
      (∀ j ∈ indices, IsIntDiv (pw1 label) F0 (B j) ∧ (∀ e ∈ B j, ¬ e.IsDiag) ∧
        (∀ w, Even (incidentLoad (B j) w)) ∧
        B j ⊆ R ∪ mapE (refEmb p) X ∧ (B j).card ≤ 214) ∧
      (∀ v, ∑ j ∈ indices, incidentLoad (B j) (refEmb p v) ≤ 99 * incidentLoad X v) ∧
      (∀ r, ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inr r)) ≤ 66) ∧
      (∀ t a, ∑ j ∈ indices, incidentLoad (B j) (Sum.inr (t,a)) ≤ 88) ∧
      (∀ D, (∀ v, incidentLoad X v ≤ D) → ∀ i : Fin (2 ^ (p + 1)),
        ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inl (Sum.inr i))) ≤
          330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p) ∧
      indices.card ≤ 57635 * (X.card + 2 * (2 ^ p) ^ 2) := by
  set X1 : Finset (Sym2 (RefU V p)) := mapE Sum.inl X
  have hX1 : ∀ e ∈ X1, ¬ e.IsDiag := loopless_mapE Sum.inl_injective hX
  set base : RefU V p := hubOf p 0
  let E := parityRefiner (X := X1) (hmap := heapH p) (L := p + 1) base hX1
    (heap_links_last X) (heap_nofix X)
  obtain ⟨indices, R, hdisj, href, hpieces, hold, htok, hcard⟩ := E.charge_layer label
  have hlift : (liftE (κ := LibIdx (RefU V p)) (mapE Sum.inl X1) :
      Finset (Sym2 (RefW V p))) = mapE (refEmb p) X := by
    simp only [liftE, X1, mapE_mapE]; rfl
  rw [hlift] at hdisj href hpieces
  have hPcard : ∀ i, (E.P i).card ≤ 22 := fun i =>
    (card_physE_le _ _).trans (by have := card_piece_le' X1 (heapH p) i; omega)
  refine ⟨indices, E.Bt label, R, hdisj, href, ?_, ?_, ?_, htok, ?_, ?_⟩
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
    rw [show (refEmb p v : RefW V p) = Sum.inl (Sum.inl (Sum.inl v)) from rfl, hold]
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
        10 * ((Fintype.card V / 2 ^ p + 1) * D) + 22 * 2 ^ (p + 1) :=
      heap_root_hub X D hD i
    have h2 : (vChain X1 (Sum.inr i)).card = 0 := by
      rw [CompressedHub.vChain_level0_hub]; rfl
    rw [h2]
    change _ ≤ 330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p
    have hp2 := pow_succ 2 p
    omega
  · refine hcard.trans ?_
    have hlib := card_evenLib_le X1 (heapH p) (p + 1) base
    have hsum := sum_card_physE_le X1 (heapH p) (p + 1) base
    have hL := heap_sum_links_compressed (p := p) X
    have hX1c : X1.card = X.card := card_mapE Sum.inl_injective X
    change (evenLib X1 (heapH p) (p + 1) base).card + 97 *
      ∑ i ∈ evenLib X1 (heapH p) (p + 1) base,
        (physE (rtP (heapH p) base) (UniversalRefiner.piece X1 (heapH p) i)).card ≤ _
    rw [hX1c] at hsum
    nlinarith

/-- The actual compatible-label producer, fixed before all divisible leftovers. -/
theorem compatible_producer (p : ℕ) (pV : V → Fin 2)
    (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag) :
    ∃ (indices : Finset (RefI V p)) (B : RefI V p → Finset (Sym2 (RefW V p)))
      (R : Finset (Sym2 (RefW V p))),
      Disjoint R (mapE (refEmb p) X) ∧
      RefinerAssembly.RefinesReserve (p := compatiblePart p pV) (F := F0)
        indices B (mapE (refEmb p) X) R ∧
      (∀ j ∈ indices, IsIntDiv (compatiblePart p pV) F0 (B j) ∧
        (∀ e ∈ B j, ¬ e.IsDiag) ∧ (∀ w, Even (incidentLoad (B j) w)) ∧
        B j ⊆ R ∪ mapE (refEmb p) X ∧ (B j).card ≤ 214) ∧
      (∀ v, ∑ j ∈ indices, incidentLoad (B j) (refEmb p v) ≤ 99 * incidentLoad X v) ∧
      (∀ r, ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inr r)) ≤ 66) ∧
      (∀ t a, ∑ j ∈ indices, incidentLoad (B j) (Sum.inr (t,a)) ≤ 88) ∧
      (∀ D, (∀ v, incidentLoad X v ≤ D) → ∀ i : Fin (2 ^ (p + 1)),
        ∑ j ∈ indices, incidentLoad (B j) (Sum.inl (Sum.inl (Sum.inr i))) ≤
          330 * ((Fintype.card V / 2 ^ p + 1) * D) + 1452 * 2 ^ p) ∧
      indices.card ≤ 57635 * (X.card + 2 * (2 ^ p) ^ 2) :=
  flexible_producer p (compatibleMid p pV) X hX

end PartitionedTriangleAbsorption.F0FlexibleCompressed
