/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingGuardPrivateStage212

/-! # Pay for every edge of the packing triangles touched by a private absorber

The closure is an actual edge set, including every freed edge. Its size is
at most four times the private size, and the guard excludes protected
non-source vertices from its whole support. No decomposition of this
closure together with the source is claimed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingPrivateClosureStage213

open Finset SignedHinge AntiEdgeSelection ReserveRetirementStage194

variable {V : Type} [DecidableEq V]

noncomputable def closure (D : Finset (Finset V)) (A : Finset (Sym2 V)) :
    Finset (Sym2 V) := by
  classical
  exact A ∪ (touching D A).biUnion triEdges

theorem touching_card_le {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (A : Finset (Sym2 V)) :
    (touching D A).card ≤ A.card := by
  classical
  have hex : ∀ s ∈ touching D A, ∃ e ∈ A, e ∈ triEdges s := by
    intro s hs
    obtain ⟨-, ht⟩ := mem_filter.mp hs
    obtain ⟨e, he, heA⟩ := not_disjoint_iff.mp ht
    exact ⟨e, heA, he⟩
  let f : touching D A → A := fun s =>
    ⟨Classical.choose (hex s.val s.property),
      (Classical.choose_spec (hex s.val s.property)).1⟩
  have hinj : Function.Injective f := by
    intro s r heq
    apply Subtype.ext
    by_contra hne
    have hs := Classical.choose_spec (hex s.val s.property)
    have hr := Classical.choose_spec (hex r.val r.property)
    have heq' := congrArg Subtype.val heq
    change Classical.choose (hex s.val s.property) =
      Classical.choose (hex r.val r.property) at heq'
    have hdis := hD.2.1 (mem_filter.mp s.property).1 (mem_filter.mp r.property).1 hne
    rw [← heq'] at hr
    exact disjoint_left.mp hdis hs.2 hr.2
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

theorem closure_card_le {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (A : Finset (Sym2 V)) :
    (closure D A).card ≤ 4 * A.card := by
  classical
  have htri : ∀ s ∈ touching D A, (triEdges s).card = 3 := by
    intro s hs
    exact Nibble.card_triEdges (hD.1 s (mem_filter.mp hs).1).1
  have hret : ((touching D A).biUnion triEdges).card ≤ 3 * (touching D A).card := by
    calc
      _ ≤ ∑ s ∈ touching D A, (triEdges s).card := card_biUnion_le
      _ = 3 * (touching D A).card := by
        calc
          _ = ∑ _s ∈ touching D A, 3 := sum_congr rfl fun s hs => htri s hs
          _ = _ := by simp [mul_comm]
  have hcount := touching_card_le p F Q D hD A
  have hu := card_union_le A ((touching D A).biUnion triEdges)
  unfold closure
  omega

theorem closure_vertex_card_le [Fintype V] {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (A : Finset (Sym2 V)) :
    (vertSet (closure D A)).card ≤ 8 * A.card := by
  have hv := SignedHinge.card_vertSet_le (closure D A)
  have he := closure_card_le p F Q D hD A
  omega

theorem closure_avoids_protected_nonroot [Fintype V] (D : Finset (Finset V))
    (P A : Finset (Sym2 V)) (S : Finset V) (b : ℕ)
    (hA : ∀ e ∈ A, ∀ v ∈ e, v ∉ vertSet P → v ∉ S)
    (hret : ∀ v ∈ S, ((touching D A).filter fun s => v ∈ s).card ≤
      if v ∈ vertSet P then b else 0) :
    ∀ v ∈ vertSet (closure D A), v ∉ vertSet P → v ∉ S := by
  intro v hv hvP hvS
  obtain ⟨e, he, hev⟩ := SignedHinge.mem_vertSet.mp hv
  rcases mem_union.mp he with heA | heR
  · exact hA e heA v hev hvP hvS
  · obtain ⟨s, hs, hes⟩ := mem_biUnion.mp heR
    have hvs : v ∈ s := by
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨ha, hb, -⟩ := TypedNibble.mem_triEdges_iff.mp hes
        rcases Sym2.mem_iff.mp hev with h | h
        · exact h ▸ ha
        · exact h ▸ hb
    have hzero := hret v hvS
    rw [if_neg hvP] at hzero
    have hempty := card_eq_zero.mp (Nat.le_zero.mp hzero)
    have hmem : s ∈ (touching D A).filter (fun s => v ∈ s) := mem_filter.mpr ⟨hs, hvs⟩
    rw [hempty] at hmem
    simp at hmem

/-- The protected private set and its complete packing closure are constructed
in one host. All bounds precede the host, source and packing. -/
theorem exists_private_with_bounded_closure {t : ℕ}
    (F : Finset (Multiset (Fin t))) (hcard : ∀ τ ∈ F, τ.card = 3)
    (hF : TypedTransformer.ThreeStepLinks F) (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∃ b N : ℕ, 0 < b ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
      (P B Q : Finset (Sym2 V)) (D : Finset (Finset V)) (S : Finset V) (d : ℝ),
      N ≤ Fintype.card V → 0 ≤ d →
      PairMoveSelectionStage85.CompatibleSupply p F G (β * Fintype.card V) →
      DegBounded B d → (5 * S.card : ℝ) + 4 * d ≤ β * Fintype.card V / 2 →
      P ⊆ G.edgeFinset → P.card ≤ m → IsIntDiv p F P → IsDecomp p F Q D →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A B ∧
        HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧
        A.card ≤ b ∧ (closure D A).card ≤ b ∧ (vertSet (closure D A)).card ≤ b ∧
        ∀ v ∈ vertSet (closure D A), v ∉ vertSet P → v ∉ S := by
  obtain ⟨a, N, ha, hprivate⟩ :=
    PackingGuardPrivateStage212.exists_private_with_packing_guard F hcard hF β hβ m
  refine ⟨8 * a, N, by omega, ?_⟩
  intro V _ _ p G _ P B Q D S d hn hd hs hB hbudget hPG hPm hdiv hD
  obtain ⟨A, hAG, hAB, hdec, habs, hAc, -, hroot, hret⟩ :=
    hprivate V p G P B Q D S d hn hd hs hB hbudget hPG hPm hdiv hD
  have hc := closure_card_le p F Q D hD A
  have hv := closure_vertex_card_le p F Q D hD A
  refine ⟨A, hAG, hAB, hdec, habs, by omega, by omega, by omega, ?_⟩
  exact closure_avoids_protected_nonroot D P A S a hroot hret


end PartitionedTriangleAbsorption.PackingPrivateClosureStage213
