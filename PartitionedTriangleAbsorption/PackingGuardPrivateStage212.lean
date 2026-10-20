/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPrivateHostStage208
public import PartitionedTriangleAbsorption.PackingOppositeShadowStage211

/-! # Private absorbers with protection of the actual packing

The forbidden opposite-edge shadow is produced from the supplied physical
packing. At protected vertices outside the source, no triangle is retired.
At protected source roots, retirement is bounded by the private size.
This controls retirement; it does not decompose its remaining freed edges.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingGuardPrivateStage212

open Finset SignedHinge AntiEdgeSelection PairMoveSelectionStage85
  TypedTransformer PackingOppositeShadowStage211 ReserveRetirementStage194

theorem exists_private_with_packing_guard {t : ℕ}
    (F : Finset (Multiset (Fin t))) (hcard : ∀ τ ∈ F, τ.card = 3)
    (hF : ThreeStepLinks F) (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∃ b N : ℕ, 0 < b ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
      (P B Q : Finset (Sym2 V)) (D : Finset (Finset V)) (S : Finset V) (d : ℝ),
      N ≤ Fintype.card V → 0 ≤ d →
      CompatibleSupply p F G (β * Fintype.card V) → DegBounded B d →
      (5 * S.card : ℝ) + 4 * d ≤ β * Fintype.card V / 2 →
      P ⊆ G.edgeFinset → P.card ≤ m → IsIntDiv p F P → IsDecomp p F Q D →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A B ∧
        HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧
        A.card ≤ b ∧ (vertSet A).card ≤ b ∧
        (∀ e ∈ A, ∀ v ∈ e, v ∉ vertSet P → v ∉ S) ∧
        ∀ v ∈ S, ((touching D A).filter fun s => v ∈ s).card ≤
          if v ∈ vertSet P then b else 0 := by
  obtain ⟨b, N, hb, hbuild⟩ :=
    TypedPrivateHostStage208.exists_private_avoiding F hcard hF β hβ m
  refine ⟨b, N, hb, ?_⟩
  intro V _ _ p G _ P B Q D S d hn hd hs hB hbudget hPG hPm hdiv hD
  classical
  have hBS : DegBounded (B ∪ shadow D S) (d + S.card) := by
    intro v
    have hnat : incidentLoad (B ∪ shadow D S) v ≤
        incidentLoad B v + incidentLoad (shadow D S) v := by
      unfold incidentLoad
      rw [filter_union]
      exact card_union_le _ _
    have hreal : (incidentLoad (B ∪ shadow D S) v : ℝ) ≤
        incidentLoad B v + incidentLoad (shadow D S) v := by exact_mod_cast hnat
    have hshadow : (incidentLoad (shadow D S) v : ℝ) ≤ S.card :=
      by exact_mod_cast shadow_degree_bound p F Q D hD S v
    exact hreal.trans (add_le_add (hB v) hshadow)
  obtain ⟨A, hAG, havoid, hdec, habs, hAc, hAv, hroot⟩ :=
    hbuild V p G P (B ∪ shadow D S) S (d + S.card) hn (by positivity) hs hBS
      (by linarith only [hbudget]) hPG hPm hdiv
  have hAB : Disjoint A B := havoid.mono_right subset_union_left
  have hAS : Disjoint A (shadow D S) := havoid.mono_right subset_union_right
  refine ⟨A, hAG, hAB, hdec, habs, hAc, hAv, hroot, ?_⟩
  intro v hv
  have hopen := avoiding_shadow_has_no_opposite_hits D S A hAS v hv
  have hret := touching_incidence_le p F Q D hD A v
  change ((touching D A).filter fun s => v ∈ s).card ≤
    (A.filter fun e => v ∈ e).card + (oppositeHits D A v).card at hret
  rw [hopen, card_empty, Nat.add_zero] at hret
  by_cases hvP : v ∈ vertSet P
  · rw [if_pos hvP]
    exact hret.trans ((card_filter_le _ _).trans hAc)
  · rw [if_neg hvP]
    have hz : A.filter (fun e => v ∈ e) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨heA, hev⟩ := mem_filter.mp he
      exact hroot e heA v hev hvP hv
    simpa only [hz, card_empty] using hret


end PartitionedTriangleAbsorption.PackingGuardPrivateStage212
