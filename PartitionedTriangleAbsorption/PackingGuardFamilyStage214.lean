/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingPrivateClosureStage213
public import PartitionedTriangleAbsorption.F0PrivateLedger

/-! # Simultaneous private absorbers with paid packing-retirement congestion

The quota counts the complete closure, not just private edges. Every edge
freed from the fixed packing is included in that closure. Its degree is
bounded during the construction. No decomposition of the freed complement
is inferred from this congestion bound.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingGuardFamilyStage214

open Finset SignedHinge AntiEdgeSelection PairMoveSelectionStage85 TypedTransformer
  F0PrivateLedger PackingPrivateClosureStage213 SparseReserveGeometry

def Good {V : Type} [Fintype V] [DecidableEq V] {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset (Finset V)) (B P A : Finset (Sym2 V)) (b : ℕ) : Prop :=
  A ⊆ G.edgeFinset ∧ Disjoint A B ∧ HasDecomp p F A ∧ HasDecomp p F (A ∪ P) ∧
    A.card ≤ b ∧ (closure D A).card ≤ b ∧ (vertSet (closure D A)).card ≤ b

theorem exists_family {t : ℕ} (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F)
    (β : ℝ) (hβ : 0 < β) (m : ℕ) :
    ∃ b N : ℕ, 0 < b ∧ ∀ (V I : Type) [Fintype V] [DecidableEq V]
      (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
      (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (_hD : IsDecomp p F Q D)
      (s : Finset I) (P : I → Finset (Sym2 V)) (B : Finset (Sym2 V))
      (d : ℝ) (M q T : ℕ), N ≤ Fintype.card V → 0 ≤ d → 0 < q →
      CompatibleSupply p F G (β * Fintype.card V) → DegBounded B d →
      b * s.card ≤ T * q →
      (5 * T : ℝ) + 4 * (d + b * (M + q)) ≤ β * Fintype.card V / 2 →
      (∀ v, roots s P v ≤ M) →
      (∀ i ∈ s, P i ⊆ G.edgeFinset ∧ (P i).card ≤ m ∧ IsIntDiv p F (P i)) →
      ∃ A : I → Finset (Sym2 V), (∀ i ∈ s, Good p F G D B (P i) (A i) b) ∧
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) ∧
        (∀ v, auxCount s P (fun i => closure D (A i)) v ≤ q) ∧
        DegBounded (s.biUnion fun i => closure D (A i)) (b * (M + q)) := by
  obtain ⟨b, N, hb, hprivate⟩ :=
    exists_private_with_bounded_closure F hcard hF β hβ m
  refine ⟨b, N, hb, ?_⟩
  intro V I _ _ p G _ Q D hD s P B d M q T hn hd hq hs hB hmass hbudget hroots hsrc
  classical
  have build : ∀ z : Finset I, z ⊆ s →
      ∃ A : I → Finset (Sym2 V), (∀ i ∈ z, Good p F G D B (P i) (A i) b) ∧
        (∀ i ∈ z, ∀ j ∈ z, i ≠ j → Disjoint (A i) (A j)) ∧
        ∀ v, auxCount z P (fun i => closure D (A i)) v ≤ q := by
    intro z
    induction z using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨fun _ => ∅, by simp, by simp, by simp [auxCount]⟩
    | @insert i z hi ih =>
      intro hzs
      have hz : z ⊆ s := fun j hj => hzs (mem_insert_of_mem hj)
      have his := hzs (mem_insert_self i z)
      obtain ⟨A, hgood, hdisj, hquota⟩ := ih hz
      let C := fun j => closure D (A j)
      have hc : ∀ j ∈ z, (C j).card ≤ b := fun j hj => (hgood j hj).2.2.2.2.2.1
      have hvc : ∀ j ∈ z, (vertSet (C j)).card ≤ b :=
        fun j hj => (hgood j hj).2.2.2.2.2.2
      have hzroots : ∀ v, roots z P v ≤ M := fun v =>
        (sum_le_sum_of_subset_of_nonneg hz (fun _ _ _ => Nat.zero_le _)).trans (hroots v)
      have hdeg : ∀ v, incidentLoad (z.biUnion C) v ≤ b * (M + q) := by
        intro v
        exact ((union_incidence_le z C v).trans (incidence_le_counts z P C b hc v)).trans
          (Nat.mul_le_mul_left b (Nat.add_le_add (hzroots v) (hquota v)))
      let Z := univ.filter fun v => q ≤ auxCount z P C v
      have hZ : Z.card ≤ T := busy_card_le z P C b q T hq hvc
        ((Nat.mul_le_mul_left b (card_le_card hz)).trans hmass)
      let L := B ∪ z.biUnion A
      have hAC : z.biUnion A ⊆ z.biUnion C := by
        intro e he
        obtain ⟨j, hj, hej⟩ := mem_biUnion.mp he
        exact mem_biUnion.mpr ⟨j, hj, mem_union_left _ hej⟩
      have hL : DegBounded L (d + b * (M + q)) := by
        intro v
        have hnat : incidentLoad L v ≤ incidentLoad B v + incidentLoad (z.biUnion A) v :=
          by unfold incidentLoad; rw [filter_union]; exact card_union_le _ _
        have hnat' := (PrivateTemplateStage69.incidentLoad_mono hAC v).trans (hdeg v)
        have hreal : (incidentLoad L v : ℝ) ≤
            incidentLoad B v + incidentLoad (z.biUnion A) v := by exact_mod_cast hnat
        have hreal' : (incidentLoad (z.biUnion A) v : ℝ) ≤ b * (M + q) :=
          by exact_mod_cast hnat'
        exact hreal.trans (add_le_add (hB v) hreal')
      obtain ⟨Ai, hAG, hAL, hdec, habs, hAc, hCc, hCv, havoid⟩ :=
        hprivate V p G (P i) L Q D Z (d + b * (M + q)) hn (by positivity) hs hL
          (by have hZ' : (Z.card : ℝ) ≤ T := by exact_mod_cast hZ
              linarith only [hZ', hbudget])
          (hsrc i his).1 (hsrc i his).2.1 (hsrc i his).2.2 hD
      have hAB : Disjoint Ai B := hAL.mono_right subset_union_left
      have hAA : ∀ j ∈ z, Disjoint Ai (A j) := fun j hj =>
        hAL.mono_right ((subset_biUnion_of_mem A hj).trans subset_union_right)
      let A' := Function.update A i Ai
      have hnew : A' i = Ai := Function.update_self _ _ _
      have hkeep : ∀ j ∈ z, A' j = A j := fun j hj =>
        Function.update_of_ne (ne_of_mem_of_not_mem hj hi) Ai A
      have hupdate : ∀ v, auxCount (insert i z) P (fun j => closure D (A' j)) v =
          auxCount z P C v +
            if v ∈ vertSet (closure D Ai) ∧ v ∉ vertSet (P i) then 1 else 0 := by
        intro v
        simp only [auxCount, sum_insert hi, hnew]
        rw [add_comm]
        congr 1
        exact sum_congr rfl fun j hj => by simp only [hkeep j hj, C]
      refine ⟨A', ?_, ?_, ?_⟩
      · intro j hj
        rcases mem_insert.mp hj with rfl | hj
        · rw [hnew]; exact ⟨hAG, hAB, hdec, habs, hAc, hCc, hCv⟩
        · rw [hkeep j hj]; exact hgood j hj
      · intro j hj k hk hjk
        by_cases hji : j = i
        · subst j
          by_cases hki : k = i
          · subst k; exact absurd rfl hjk
          · have hkz := (mem_insert.mp hk).resolve_left hki
            rw [hnew, hkeep k hkz]; exact hAA k hkz
        · have hjz := (mem_insert.mp hj).resolve_left hji
          by_cases hki : k = i
          · subst k
            rw [hkeep j hjz, hnew]; exact (hAA j hjz).symm
          · have hkz := (mem_insert.mp hk).resolve_left hki
            rw [hkeep j hjz, hkeep k hkz]; exact hdisj j hjz k hkz hjk
      · intro v
        rw [hupdate]
        by_cases hv : v ∈ vertSet (closure D Ai) ∧ v ∉ vertSet (P i)
        · have hnZ : v ∉ Z := havoid v hv.1 hv.2
          have hlt : auxCount z P C v < q := by
            have hnot : ¬ q ≤ auxCount z P C v :=
              fun h => hnZ (mem_filter.mpr ⟨mem_univ _, h⟩)
            omega
          rw [if_pos hv]; exact Nat.succ_le_of_lt hlt
        · rw [if_neg hv, Nat.add_zero]; exact hquota v
  obtain ⟨A, hgood, hdisj, hquota⟩ := build s subset_rfl
  refine ⟨A, hgood, hdisj, hquota, fun v => ?_⟩
  have hc : ∀ i ∈ s, (closure D (A i)).card ≤ b :=
    fun i hi => (hgood i hi).2.2.2.2.2.1
  have h := ((union_incidence_le s (fun i => closure D (A i)) v).trans
    (incidence_le_counts s P (fun i => closure D (A i)) b hc v)).trans
      (Nat.mul_le_mul_left b (Nat.add_le_add (hroots v) (hquota v)))
  exact_mod_cast h


end PartitionedTriangleAbsorption.PackingGuardFamilyStage214
