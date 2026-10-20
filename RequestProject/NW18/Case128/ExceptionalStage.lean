/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128.ForcedBound

@[expose] public section

/-!
# Case (5): the exceptional stage (pre-clean followed by the stars)

For the exceptional set `S = exceptional G p τ` of a locally optimal partition, we first remove
the edges inside `S` by the pre-clean triangles (`stage_preclean`, with the large colours of
`large_pairs`) and then all remaining edges at `S` by the star family (`stage_stars`).  The
union `P` of the two families covers every edge at `S`, has load at most `3|S|+1` at every
vertex outside `S`, and consumes at most the available six-fold quotas.
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open ClassRepresentativesStage65 CleanupSupplyStage140 ExceptionalQuotaStage142 AntiEdgeSelection
open ExceptionalGeometryStage141

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
lemma card_family_le_of_meet (D : Finset (Finset V)) (S : Finset V) (k : ℕ)
    (hmeet : ∀ t ∈ D, ∃ x ∈ S, x ∈ t) (hload : ∀ x ∈ S, (D.filter fun t => x ∈ t).card ≤ k) :
    D.card ≤ S.card * k := by
  have hsub : D ⊆ S.biUnion (fun x => D.filter fun t => x ∈ t) := by
    intro t ht
    obtain ⟨x, hx, hxt⟩ := hmeet t ht
    exact mem_biUnion.mpr ⟨x, hx, mem_filter.mpr ⟨ht, hxt⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  have := sum_le_card_nsmul S (fun x => (D.filter fun t => x ∈ t).card) k hload
  simpa using this

/-- **The exceptional stage.** -/
theorem stage_exceptional (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (ρ τ : ℝ) (L D : ℕ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 1920) (hτ : 0 < τ)
    (hn : 0 < Fintype.card V)
    (hdiv : IsIntDiv OnePart.part1 OnePart.triFam G.edgeFinset)
    (hmin : (3 / 4 : ℝ) * Fintype.card V ≤ G.minDegree)
    (hint : ((internal p G.edgeFinset).card : ℝ) ≤ ρ * (Fintype.card V : ℝ) ^ 2)
    (hloc : ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j)
    (h1 : 11 * ρ * Fintype.card V + 3 * ((exceptional G p τ).card : ℝ) / 2 ≤
      Fintype.card V / 120)
    (h2 : 12 * ρ * Fintype.card V + ((exceptional G p τ).card : ℝ) / 2 ≤
      τ * Fintype.card V / 180)
    (h3 : ((exceptional G p τ).card : ℝ) ≤ τ * Fintype.card V / 1800)
    (h4 : 8 * (((exceptional G p τ).card : ℝ) + 1) + (exceptional G p τ).card ≤
      Fintype.card V / 20)
    (hL : (1 / 4 + 8 * ρ) * Fintype.card V ≤ L)
    (hD : (24 * ρ + τ) * Fintype.card V + 4 * ((exceptional G p τ).card : ℝ) + 2 ≤ D)
    (h5 : 2 * (L : ℝ) + 4 * ((D : ℝ) + (exceptional G p τ).card) + 2 <
      3 / 4 * Fintype.card V - 2 * ((exceptional G p τ).card : ℝ)) :
    ∃ P : Finset (Finset V),
      (∀ t ∈ P, G.IsNClique 3 t) ∧ (P : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ u v, G.Adj u v → (u ∈ exceptional G p τ ∨ v ∈ exceptional G p τ) →
        s(u, v) ∈ P.biUnion triEdges) ∧
      (∀ y, y ∉ exceptional G p τ →
        (P.filter (fun t => y ∈ t)).card ≤ 3 * (exceptional G p τ).card + 1) ∧
      (∀ i, 6 * ((P.filter (SameSide p i)).card : ℤ) ≤ sixQuota p G.edgeFinset i) := by
  classical
  set S := exceptional G p τ with hSdef
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hs0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hdeg : ∀ v, (3 / 4 : ℝ) * n ≤ G.degree v :=
    fun v => hmin.trans (by exact_mod_cast G.minDegree_le_degree v)
  have hsize := class_upper_average G p ρ hρ0 hn hdeg hint
  have hlow := class_lower_average G p ρ hρ0 hn hdeg hint
  have hSmem : ∀ v ∈ S, τ * n < classLoad p G v (p v) := by
    intro v hv
    have := (mem_filter.mp hv).2
    rwa [internalNeighbours_card] at this
  have hsix0 : ∀ i, (0 : ℝ) ≤ (sixQuota p G.edgeFinset i : ℝ) := by
    intro i
    refine le_trans ?_ (sixQuota_ge_sum G p S i hdeg)
    refine sum_nonneg fun v _ => ?_
    have := hdeg v
    have : (0 : ℝ) ≤ (farMissing G p S i v).card := Nat.cast_nonneg _
    linarith
  -- the pre-clean
  let C : Fin 3 → Prop := fun i => 180 * (S.card : ℝ) ^ 2 ≤ (sixQuota p G.edgeFinset i : ℝ)
  have hC : S.Nonempty → ∃ ℓ₀ : Fin 3, ∀ i, i ≠ ℓ₀ → C i := fun _ =>
    large_pairs G p S ρ τ hτ hdeg hlow hSmem h2 h3
  obtain ⟨D1, hcl1, hdis1, hcov1, hdeg1, hloadS1, hside1, hmeet1⟩ :=
    stage_preclean G p S C ρ hρ0 hρ hn hloc hmin hsize hC h4
  have hD13 : ∀ t ∈ D1, t.card = 3 := fun t ht => (hcl1 t ht).2
  set P1 := D1.biUnion triEdges with hP1
  have hP1sub : P1 ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hcl1 t ht)
  have hincP1 : ∀ v, (incidentLoad P1 v : ℝ) ≤ 4 * S.card + 2 := by
    intro v
    have := hdeg1 v
    simpa [incidentLoad] using this
  set G1 := G.deleteEdges (P1 : Set (Sym2 V)) with hG1
  have hE1 : G1.edgeFinset = G.edgeFinset \ P1 := by
    show (G.deleteEdges (P1 : Set (Sym2 V))).edgeFinset = _
    rw [SimpleGraph.edgeFinset_deleteEdges]
  have hadj1 : ∀ u v, G1.Adj u v ↔ G.Adj u v ∧ s(u, v) ∉ P1 := by
    intro u v
    rw [hG1, SimpleGraph.deleteEdges_adj]
    simp
  have hindep : ∀ u ∈ S, ∀ w ∈ S, ¬ G1.Adj u w := by
    intro u hu w hw h
    obtain ⟨h1', h2'⟩ := (hadj1 u w).mp h
    exact h2' (hcov1 u hu w hw h1')
  have hdegadd : ∀ v, G1.degree v + incidentLoad P1 v = G.degree v :=
    fun v => degree_deleteEdges_add G P1 hP1sub v
  have hincS : ∀ v ∈ S, incidentLoad P1 v ≤ 2 * S.card := by
    intro v hv
    rw [hP1, incidentLoad_family D1 hD13 hdis1 v]
    have := hloadS1 v hv
    omega
  have hdiv1 : IsIntDiv OnePart.part1 OnePart.triFam G1.edgeFinset := by
    rw [hE1]
    exact isIntDiv_sdiff_of_hasDecomp hdiv (hasDecomp_of_family D1 hD13 hdis1) hP1sub
  have heven1 : ∀ v, G1.degree v = 2 * (G1.degree v / 2) := by
    have hloop : ∀ e ∈ G1.edgeFinset, ¬ e.IsDiag :=
      fun _ he => G1.not_isDiag_of_mem_edgeFinset he
    have hE3 := (OnePart.isIntDiv_part1_iff _ hloop).mp hdiv1
    intro v
    have h := hE3.2 v
    rw [IndependentStarQuotaStage144.incident_degree] at h
    obtain ⟨k, hk⟩ := h
    omega
  have hsix1 : ∀ i, sixQuota p G1.edgeFinset i =
      sixQuota p G.edgeFinset i - 6 * ((D1.filter (SameSide p i)).card : ℤ) := by
    intro i
    rw [hE1]
    exact sixQuota_sdiff_family p G.edgeFinset D1 hD13 hdis1 hP1sub i
  have hD1card : D1.card ≤ S.card * S.card :=
    card_family_le_of_meet D1 S S.card hmeet1 hloadS1
  have hSS1 : ∀ i, 180 * ((D1.filter (SameSide p i)).card : ℝ) ≤
      (sixQuota p G.edgeFinset i : ℝ) := by
    intro i
    by_cases hCi : C i
    · have hle : (D1.filter (SameSide p i)).card ≤ S.card * S.card :=
        (card_filter_le _ _).trans hD1card
      have hle' : ((D1.filter (SameSide p i)).card : ℝ) ≤ (S.card : ℝ) ^ 2 := by
        rw [sq]; exact_mod_cast hle
      have : 180 * (S.card : ℝ) ^ 2 ≤ (sixQuota p G.edgeFinset i : ℝ) := hCi
      linarith
    · have hempty : D1.filter (SameSide p i) = ∅ := by
        rw [filter_eq_empty_iff]
        intro t ht hside
        exact hCi (hside1 t ht i hside)
      rw [hempty, card_empty, Nat.cast_zero, mul_zero]
      exact hsix0 i
  -- degree facts at `S`
  have hdegS : ∀ v ∈ S, 4 * S.card ≤ G.degree v := by
    intro v _
    have : (4 * S.card : ℝ) ≤ G.degree v := by
      have := hdeg v
      linarith
    exact_mod_cast this
  have hdeg1R : ∀ v ∈ S, (3 / 4 : ℝ) * n - 2 * S.card ≤ G1.degree v := by
    intro v hv
    have e1 : (G1.degree v : ℝ) + incidentLoad P1 v = G.degree v := by
      exact_mod_cast hdegadd v
    have e2 : (incidentLoad P1 v : ℝ) ≤ 2 * S.card := by exact_mod_cast hincS v hv
    have := hdeg v
    linarith
  -- the star stage
  obtain ⟨D2, hcl2, hdis2, hcov2, hload2, hside2⟩ := stage_stars G1 p S hindep hdiv1 L D
    (by
      intro v hv
      have e1 : classLoad p G1 v (p v) ≤ classLoad p G v (p v) :=
        classLoad_deleteEdges_le G (P1 : Set (Sym2 V)) p v (p v)
      have e2 := four_classLoad_own_le p G hloc v
      have e3 := hdegadd v
      have e4 := hincS v hv
      have e5 := hdegS v hv
      have e6 := heven1 v
      omega)
    (by
      intro v hv i
      have e1 := classLoad_deleteEdges_le G (P1 : Set (Sym2 V)) p v (partner i (p v))
      have e2 := classLoad_le_classSet p G v (partner i (p v))
      have e3 := hsize (partner i (p v))
      have e4 := hdeg1R v hv
      have e5 : (2 * classLoad p G1 v (partner i (p v)) : ℝ) ≤ G1.degree v := by
        have : (classLoad p G1 v (partner i (p v)) : ℝ) ≤ (classSet p (partner i (p v))).card :=
          by exact_mod_cast e1.trans e2
        have : (S.card : ℝ) * 9 + 8 ≤ n / 20 := by linarith
        nlinarith
      have e6 : 2 * classLoad p G1 v (partner i (p v)) ≤ G1.degree v := by exact_mod_cast e5
      have e7 := heven1 v
      omega)
    (by
      intro i
      have hf := forced_sum_le G G1 p S ρ hρ0 hloc hsize hdeg
        (fun v _ j => classLoad_deleteEdges_le G (P1 : Set (Sym2 V)) p v j)
        (fun v hv => by have := hdegadd v; have := hincS v hv; omega) heven1 h1 i
      have hR : 6 * ((∑ v ∈ S, (classLoad p G1 v (p v) + classLoad p G1 v (partner i (p v)) -
          G1.degree v / 2) : ℕ) : ℝ) ≤ ((sixQuota p G1.edgeFinset i : ℤ) : ℝ) := by
        rw [hsix1 i]
        push_cast
        have := hSS1 i
        have := hsix0 i
        push_cast at hf
        linarith
      exact_mod_cast hR)
    (fun j => by
      have : ((classSet p j).card : ℝ) ≤ L := (hsize j).trans hL
      exact_mod_cast this)
    (by
      intro v hv w hw
      have hwS : w ∉ S := fun hwS => hindep v hv w hwS hw
      have e1 := missingOutside_deleteEdges_le G P1 p w
      have e2 := typical_missing_bound G p ρ τ hρ0 hn hdeg hint w hwS
      have e3 := hincP1 w
      have : ((missingOutside G1 p w).card : ℝ) ≤ D := by
        have : ((missingOutside G1 p w).card : ℝ) ≤ (missingOutside G p w).card +
            incidentLoad P1 w := by exact_mod_cast e1
        linarith
      exact_mod_cast this)
    (by
      intro v hv
      have := hdeg1R v hv
      have : (2 * L + 4 * (D + S.card) + 2 : ℝ) < G1.degree v := by linarith
      exact_mod_cast this)
  -- assembling the two families
  have hD2sub : ∀ t ∈ D2, triEdges t ⊆ G.edgeFinset \ P1 := by
    intro t ht
    rw [← hE1]
    exact triEdges_subset_of_isNClique (hcl2 t ht)
  refine ⟨D1 ∪ D2, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases mem_union.mp ht with ht | ht
    · exact hcl1 t ht
    · exact (hcl2 t ht).mono (SimpleGraph.deleteEdges_le _)
  · rw [coe_union]
    refine hdis1.union hdis2 fun t ht t' ht' _ => ?_
    exact disjoint_of_subset_left (subset_biUnion_of_mem triEdges (mem_coe.mp ht))
      (disjoint_of_subset_right (hD2sub t' (mem_coe.mp ht')) disjoint_sdiff)
  · intro u v huv h
    rw [union_biUnion]
    by_cases hin : s(u, v) ∈ P1
    · exact mem_union_left _ hin
    · have h1' : G1.Adj u v := (hadj1 u v).mpr ⟨huv, hin⟩
      refine mem_union_right _ ?_
      rcases h with hu | hv
      · exact hcov2 u hu v h1'
      · rw [Sym2.eq_swap]; exact hcov2 v hv u h1'.symm
  · intro y hy
    have e1 := card_filter_union_le D1 D2 (fun t => y ∈ t)
    have e2 := hload2 y hy
    have e3 : incidentLoad P1 y ≤ 4 * S.card + 2 := by exact_mod_cast hincP1 y
    rw [hP1, incidentLoad_family D1 hD13 hdis1 y] at e3
    omega
  · intro i
    have e1 := card_filter_union_le D1 D2 (SameSide p i)
    have e2 := hside2 i
    rw [hsix1 i] at e2
    have e1' : ((((D1 ∪ D2).filter (SameSide p i)).card : ℕ) : ℤ) ≤
        ((D1.filter (SameSide p i)).card : ℤ) + ((D2.filter (SameSide p i)).card : ℤ) := by
      exact_mod_cast e1
    linarith

end NashWilliams18.C128
