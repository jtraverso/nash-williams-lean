/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case128.PrecleanStage

@[expose] public section

/-!
# Case (5): the star stage with integer quotas

For a graph `H` in which the exceptional set `S` is independent, the integer quotas of
`MatchedQuotaStage140.exists_quotas`, an allocation from `StarCutsStage143.exists_star_counts`
and the star family of `exists_star_family` give an edge-disjoint family of triangles covering
every edge at `S` whose number of `i`-matched triangles is at most a sixth of the six-fold quota
`sixQuota p E(H) i`.
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 GraphStarInventoryStage144
open ClassRepresentativesStage65 CleanupSupplyStage140 ExceptionalQuotaStage142

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The star stage.** -/
theorem stage_stars (H : SimpleGraph V) [DecidableRel H.Adj] (p : V → Fin 4)
    (S : Finset V) (hS : ∀ u ∈ S, ∀ w ∈ S, ¬ H.Adj u w)
    (hdiv : IsIntDiv OnePart.part1 OnePart.triFam H.edgeFinset)
    (L D : ℕ)
    (ha : ∀ v ∈ S, classLoad p H v (p v) ≤ H.degree v / 2)
    (hb : ∀ v ∈ S, ∀ i, classLoad p H v (partner i (p v)) ≤ H.degree v / 2)
    (hforced : ∀ i, 6 * ((∑ v ∈ S, (classLoad p H v (p v) + classLoad p H v (partner i (p v)) -
        H.degree v / 2) : ℕ) : ℤ) ≤ sixQuota p H.edgeFinset i)
    (hclasses : ∀ j, (classSet p j).card ≤ L)
    (hmissing : ∀ v ∈ S, ∀ w, H.Adj v w → (missingOutside H p w).card ≤ D)
    (hmargin : ∀ v ∈ S, 2 * L + 4 * (D + S.card) + 2 < H.degree v) :
    ∃ Q : Finset (Finset V),
      (∀ t ∈ Q, H.IsNClique 3 t) ∧ (Q : Set (Finset V)).PairwiseDisjoint triEdges ∧
      (∀ v ∈ S, ∀ w, H.Adj v w → s(v, w) ∈ Q.biUnion triEdges) ∧
      (∀ y, y ∉ S → (Q.filter (fun t => y ∈ t)).card ≤ S.card) ∧
      (∀ i, 6 * ((Q.filter (SameSide p i)).card : ℤ) ≤ sixQuota p H.edgeFinset i) := by
  classical
  have hloop : ∀ e ∈ H.edgeFinset, ¬ e.IsDiag :=
    fun _ he => H.not_isDiag_of_mem_edgeFinset he
  have hE3 := (OnePart.isIntDiv_part1_iff _ hloop).mp hdiv
  have heven : ∀ v, H.degree v = 2 * (H.degree v / 2) := by
    intro v
    have h := hE3.2 v
    rw [IndependentStarQuotaStage144.incident_degree] at h
    obtain ⟨k, hk⟩ := h
    omega
  -- sixQuota is nonnegative
  have hsurplus : ∀ i : Fin 3, 3 * (cuts p H.edgeFinset i).card ≤ 2 * H.edgeFinset.card := by
    intro i
    have h := hforced i
    have h0 : (0 : ℤ) ≤ 6 * ((∑ v ∈ S, (classLoad p H v (p v) +
        classLoad p H v (partner i (p v)) - H.degree v / 2) : ℕ) : ℤ) := by positivity
    have := h0.trans h
    unfold sixQuota at this
    omega
  obtain ⟨q, hq6, hqsum⟩ := exists_quotas p H.edgeFinset hloop hE3 hsurplus
  have hq : ∀ i, sixQuota p H.edgeFinset i = 6 * (q i : ℤ) := by
    intro i
    have := hq6 i
    unfold sixQuota
    omega
  -- the allocation
  let a : S → ℕ := fun v => classLoad p H v (p v)
  let h : S → ℕ := fun v => H.degree v / 2
  let b : S → Fin 3 → ℕ := fun v i => classLoad p H v (partner i (p v))
  have hsumS : ∀ f : V → ℕ, (∑ v : S, f v) = ∑ v ∈ S, f v := fun f =>
    Finset.sum_coe_sort S f
  have hforced' : ∀ i, (∑ v, (a v + b v i - h v)) ≤ q i := by
    intro i
    have h1 := hforced i
    rw [hq i] at h1
    have h2 : (∑ v, (a v + b v i - h v)) = ∑ v ∈ S, (classLoad p H v (p v) +
        classLoad p H v (partner i (p v)) - H.degree v / 2) :=
      hsumS (fun v => classLoad p H v (p v) + classLoad p H v (partner i (p v)) -
        H.degree v / 2)
    rw [h2]
    omega
  have htotal : (∑ v, a v) ≤ ∑ i, q i := by
    rw [hqsum]
    have h1 : (∑ v, a v) = ∑ v ∈ S, AntiEdgeSelection.incidentLoad
        (internal p H.edgeFinset) v := by
      rw [← hsumS (fun v => AntiEdgeSelection.incidentLoad (internal p H.edgeFinset) v)]
      exact sum_congr rfl fun v _ => internal_inventory p H v
    rw [h1]
    apply IndependentStarQuotaStage144.independent_incident_bound
    · exact fun e he => hloop e (mem_filter.mp he).1
    · intro u hu w hw he
      exact hS u hu w hw (H.mem_edgeFinset.mp (mem_filter.mp he).1)
  obtain ⟨x, hrow, hx, hcol⟩ := StarCutsStage143.exists_star_counts a h b q
    (fun v => by
      have := degree_inventory p H v.1
      have := heven v.1
      simp only [a, b, h]
      omega)
    (fun v => ha v.1 v.2) (fun v i => hb v.1 v.2 i) hforced' htotal
  obtain ⟨Q, hcl, hdis, hcov, hload, hside⟩ := exists_star_family H p S hS x L D
    (fun v _ => heven v) ha hrow hx hclasses hmissing hmargin
  refine ⟨Q, hcl, hdis, hcov, hload, fun i => ?_⟩
  rw [hq i]
  have := (hside i).trans (hcol i)
  omega

end NashWilliams18.C128
