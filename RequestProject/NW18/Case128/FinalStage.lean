/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case128.StarStage

/-!
# Case (5): the final cleanup after the exceptional stage

Given a family `P` of edge-disjoint triangles covering every edge at the exceptional set `S`,
with small load outside `S` and consuming at most the available matched quotas, the remaining
graph `G − ⋃P` satisfies the hypotheses of `CleanupAssemblyStage140.exists_balanced_cleanup`.
Gluing its output with `P` gives the conclusion of `ExceptionalCleanup128` (for a fixed graph).
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open ClassRepresentativesStage65 CleanupSupplyStage140 ExceptionalQuotaStage142 AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma card_filter_union_le (A B : Finset (Finset V)) (f : Finset V → Prop) [DecidablePred f] :
    ((A ∪ B).filter f).card ≤ (A.filter f).card + (B.filter f).card := by
  rw [filter_union]; exact card_union_le _ _

/-- **The final stage.** -/
theorem stage_final (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (S : Finset V)
    (ρ τ : ℝ) (m b d q : ℕ)
    (hdiv : IsIntDiv OnePart.part1 OnePart.triFam G.edgeFinset)
    (hint : ((internal p G.edgeFinset).card : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2)
    (htyp : ∀ v, v ∉ S → (classLoad p G v (p v) : ℝ) ≤ τ * Fintype.card V)
    (hcand : ∀ u v, u ∉ S → v ∉ S → ∀ j, j ≠ p u → j ≠ p v →
      (b : ℝ) + 4 * m ≤ (candidates G p u v j).card)
    (hd : τ * Fintype.card V < d + 1)
    (hbudget : 2 * ρ * (Fintype.card V : ℝ) ^ 2 + 2 * (d + 2 * q) * q < b * q)
    (P : Finset (Finset V)) (hP : ∀ t ∈ P, G.IsNClique 3 t)
    (hPdisj : (P : Set (Finset V)).PairwiseDisjoint triEdges)
    (hPcov : ∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S) → s(u, v) ∈ P.biUnion triEdges)
    (hPload : ∀ y, y ∉ S → (P.filter (fun t => y ∈ t)).card ≤ m)
    (hPside : ∀ i, 6 * ((P.filter (SameSide p i)).card : ℤ) ≤ sixQuota p G.edgeFinset i) :
    ∃ Q : Finset (Finset V),
        (∀ s ∈ Q, G.IsNClique 3 s) ∧
        (Q : Set (Finset V)).PairwiseDisjoint triEdges ∧
        (∀ u v, G.Adj u v → (u ∈ S ∨ v ∈ S ∨ p u = p v) → s(u, v) ∈ Q.biUnion triEdges) ∧
        (∀ x, x ∉ S → (Q.filter (fun s => x ∈ s)).card ≤ m + d + q) ∧
        (edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 1 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 2 3 =
          edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 2 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 1 3) ∧
        (edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 1 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 2 3 =
          edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 0 3 +
            edgeVec p (G.edgeFinset \ Q.biUnion triEdges) 1 2) := by
  classical
  have hP3 : ∀ t ∈ P, t.card = 3 := fun t ht => (hP t ht).2
  set PS := P.biUnion triEdges with hPS
  have hPSsub : PS ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hP t ht)
  set G2 := G.deleteEdges (PS : Set (Sym2 V)) with hG2
  have hE2 : G2.edgeFinset = G.edgeFinset \ PS := by
    show (G.deleteEdges (PS : Set (Sym2 V))).edgeFinset = _
    rw [SimpleGraph.edgeFinset_deleteEdges]
  have hdiv2 : IsIntDiv OnePart.part1 OnePart.triFam G2.edgeFinset := by
    rw [hE2]
    exact isIntDiv_sdiff_of_hasDecomp hdiv (hasDecomp_of_family P hP3 hPdisj) hPSsub
  have hload2 : ∀ y, y ∉ S → incidentLoad PS y ≤ 2 * m := by
    intro y hy
    rw [hPS, incidentLoad_family P hP3 hPdisj]
    have := hPload y hy
    omega
  have hadj2 : ∀ u v, G2.Adj u v ↔ G.Adj u v ∧ s(u, v) ∉ PS := by
    intro u v
    rw [hG2, SimpleGraph.deleteEdges_adj]
    simp
  have hnotS : ∀ u v, G2.Adj u v → u ∉ S ∧ v ∉ S := by
    intro u v huv
    obtain ⟨h1, h2⟩ := (hadj2 u v).mp huv
    exact ⟨fun hu => h2 (hPcov u v h1 (Or.inl hu)), fun hv => h2 (hPcov u v h1 (Or.inr hv))⟩
  -- hypotheses of the balanced cleanup
  have hsurplus : ∀ i : Fin 3, 3 * (cuts p G2.edgeFinset i).card ≤ 2 * G2.edgeFinset.card := by
    intro i
    have h := sixQuota_sdiff_family p G.edgeFinset P hP3 hPdisj hPSsub i
    rw [← hPS, ← hE2] at h
    have h' := hPside i
    have : 0 ≤ sixQuota p G2.edgeFinset i := by rw [h]; linarith
    unfold sixQuota at this
    omega
  have hroot : ∀ x, incidentLoad (internal p G2.edgeFinset) x ≤ d := by
    intro x
    rw [← internal_inventory]
    by_cases hx : x ∈ S
    · have : classLoad p G2 x (p x) = 0 := by
        unfold classLoad
        rw [card_eq_zero, filter_eq_empty_iff]
        intro w hw
        rw [SimpleGraph.mem_neighborFinset] at hw
        exact absurd hx (hnotS x w hw).1
      omega
    · have h1 := classLoad_deleteEdges_le G (PS : Set (Sym2 V)) p x (p x)
      have h2 := htyp x hx
      have h3 : (classLoad p G x (p x) : ℝ) < d + 1 := lt_of_le_of_lt h2 hd
      have h4 : classLoad p G x (p x) < d + 1 := by exact_mod_cast h3
      exact (h1.trans (Nat.lt_succ_iff.mp h4))
  have hsupply : ∀ u v k, G2.Adj u v → p u = p v → k ≠ p u →
      b ≤ (RequestPackingStage140.candidates p G2 u v k).card := by
    intro u v k huv hpuv hk
    obtain ⟨hu, hv⟩ := hnotS u v huv
    have h1 := candidates_deleteEdges_ge G p PS u v k
    have h2 := hcand u v hu hv k hk (hpuv ▸ hk)
    have h3 : (incidentLoad PS u : ℝ) ≤ 2 * m := by exact_mod_cast hload2 u hu
    have h4 : (incidentLoad PS v : ℝ) ≤ 2 * m := by exact_mod_cast hload2 v hv
    have : (b : ℝ) ≤ (RequestPackingStage140.candidates p G2 u v k).card := by
      linarith
    exact_mod_cast this
  have hbud : 2 * (internal p G2.edgeFinset).card + 2 * (d + 2 * q) * q < b * q := by
    have h1 : (internal p G2.edgeFinset).card ≤ (internal p G.edgeFinset).card := by
      apply card_le_card
      rw [hE2]
      exact filter_subset_filter _ sdiff_subset
    have h2 : ((internal p G2.edgeFinset).card : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2 :=
      (by exact_mod_cast h1 : ((internal p G2.edgeFinset).card : ℝ) ≤
        (internal p G.edgeFinset).card).trans hint
    have : (2 * (internal p G2.edgeFinset).card + 2 * (d + 2 * q) * q : ℝ) < b * q := by
      linarith
    exact_mod_cast this
  obtain ⟨Pc, hPcsub, ⟨Dc, hDcT, hDcdisj, hDcU⟩, hPcdeg, hPccov, hbal1, hbal2⟩ :=
    CleanupAssemblyStage140.exists_balanced_cleanup G2 p b d q hdiv2 hsurplus hroot hsupply hbud
  have hDc3 : ∀ t ∈ Dc, t.card = 3 := fun t ht => (hDcT t ht).1
  have hDcsub : ∀ t ∈ Dc, triEdges t ⊆ G.edgeFinset \ PS := by
    intro t ht
    rw [← hE2]
    exact (subset_biUnion_of_mem triEdges ht).trans (by rw [hDcU]; exact hPcsub)
  refine ⟨P ∪ Dc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact hP t ht
    · exact isNClique_of_triEdges_subset (hDc3 t ht) ((hDcsub t ht).trans sdiff_subset)
  · rw [coe_union]
    refine hPdisj.union hDcdisj fun t ht t' ht' _ => ?_
    exact disjoint_of_subset_left (subset_biUnion_of_mem triEdges (mem_coe.mp ht))
      (disjoint_of_subset_right (hDcsub t' (mem_coe.mp ht')) disjoint_sdiff)
  · intro u v huv h
    rw [union_biUnion]
    by_cases hin : s(u, v) ∈ PS
    · exact mem_union_left _ hin
    · have h2 : G2.Adj u v := (hadj2 u v).mpr ⟨huv, hin⟩
      obtain ⟨hu, hv⟩ := hnotS u v h2
      have hp : p u = p v := by tauto
      refine mem_union_right _ ?_
      rw [hDcU]
      exact hPccov u v h2 hp
  · intro x hx
    have h1 := hPload x hx
    have h2 := incidentLoad_family Dc hDc3 hDcdisj x
    rw [hDcU] at h2
    have h3 : ((Pc.filter fun e => x ∈ e).card : ℝ) ≤ 2 * d + 2 * q := hPcdeg x
    have h4 : incidentLoad Pc x ≤ 2 * d + 2 * q := by
      unfold incidentLoad; exact_mod_cast h3
    have := card_filter_union_le P Dc (fun s => x ∈ s)
    omega
  · have hres : G.edgeFinset \ (P ∪ Dc).biUnion triEdges = G2.edgeFinset \ Pc := by
      rw [union_biUnion, hDcU, hE2, sdiff_sdiff_left]; rfl
    rw [hres]; exact hbal1
  · have hres : G.edgeFinset \ (P ∪ Dc).biUnion triEdges = G2.edgeFinset \ Pc := by
      rw [union_biUnion, hDcU, hE2, sdiff_sdiff_left]; rfl
    rw [hres]; exact hbal2

end NashWilliams18.C128
