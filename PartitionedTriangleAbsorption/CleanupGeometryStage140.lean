/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupSupplyStage140
public import PartitionedTriangleAbsorption.CleanupHierarchyStage140
public import PartitionedTriangleAbsorption.CleanupAssemblyStage140
public import PartitionedTriangleAbsorption.ChildBalanceStage128

/-! # A dense graph with a sparse internal four-part partition

All cleanup choices and budgets are produced from graph data. The result
applies when each vertex has few neighbours in its own part. Ordinary triangle
divisibility suffices; the two refined balances are proved for the constructed
residual. This does not settle the general typed absorption statement.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupGeometryStage140

open Finset AntiEdgeSelection ClassRepresentativesStage65 MatchedQuotaStage140
open CleanupHierarchyStage140

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem internal_load_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (x : V) :
    incidentLoad (internal p G.edgeFinset) x =
      (CleanupSupplyStage140.internalNeighbours G p x).card := by
  classical
  symm
  unfold incidentLoad
  apply card_bij (fun w _ => s(x, w))
  · intro w hw
    obtain ⟨hn, hp⟩ := mem_inter.mp hw
    have hG : G.Adj x w := (G.mem_neighborFinset x w).mp hn
    have hp' : p w = p x := (mem_filter.mp hp).2
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨G.mem_edgeFinset.mpr hG, ?_⟩, ?_⟩
    · simpa only [Sym2.map_mk, Sym2.mk_isDiag_iff] using hp'.symm
    · simp
  · intro a _ b _ h
    rcases Sym2.eq_iff.mp h with ⟨_, hab⟩ | ⟨hxb, hax⟩
    · exact hab
    · exact hax.trans hxb
  · intro e he
    obtain ⟨heI, hx⟩ := mem_filter.mp he
    obtain ⟨heG, hp⟩ := mem_filter.mp heI
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.mem_iff] at hx
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hp
      have hG : G.Adj a b := G.mem_edgeFinset.mp heG
      rcases hx with hxa | hxb
      · subst x
        refine ⟨b, mem_inter.mpr ⟨(G.mem_neighborFinset a b).mpr hG, ?_⟩, rfl⟩
        exact mem_filter.mpr ⟨mem_univ _, hp.symm⟩
      · subst x
        refine ⟨a, mem_inter.mpr ⟨(G.mem_neighborFinset b a).mpr hG.symm, ?_⟩, ?_⟩
        · exact mem_filter.mpr ⟨mem_univ _, hp⟩
        · exact Sym2.eq_swap

theorem candidates_eq (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (k : Fin 4) :
    CleanupSupplyStage140.candidates G p u v k =
      RequestPackingStage140.candidates p G u v k := by
  classical
  ext w
  simp only [CleanupSupplyStage140.candidates, RequestPackingStage140.candidates,
    mem_inter, classSet, mem_filter, mem_univ, true_and]
  rw [G.mem_neighborFinset u w, G.mem_neighborFinset v w]
  constructor
  · rintro ⟨⟨hp, hu⟩, hv⟩
    exact ⟨hu, hv.symm, hp⟩
  · rintro ⟨hu, hv, hp⟩
    exact ⟨⟨hp, hu⟩, hv.symm⟩

/-- A uniform extension of the proper four-colour consumer to partitions with
small maximum internal degree. The cleanup packing is constructed in the proof. -/
theorem sparse_internal_decomposition :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 / 1000 ∧ ∃ N : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W], N ≤ Fintype.card W →
        ∀ (G : SimpleGraph W) [DecidableRel G.Adj] (p : W → Fin 4),
          (3 / 4 : ℝ) * Fintype.card W ≤ (G.minDegree : ℝ) →
          IsIntDiv OnePart.part1 OnePart.triFam G.edgeFinset →
          (∀ x, (incidentLoad (internal p G.edgeFinset) x : ℝ) ≤
            eps * Fintype.card W) →
          HasDecomp OnePart.part1 OnePart.triFam G.edgeFinset := by
  obtain ⟨eta, heta, _, N₁, hconsume⟩ :=
    CleanupAssemblyStage140.decomposition_of_uniform_supply
  obtain ⟨eps, heps, heps1, a, _, N₂, hnum⟩ := exists_hierarchy eta heta
  refine ⟨eps, heps, heps1, max N₁ N₂, ?_⟩
  intro W _ _ hW G _ p hmin hdiv hint
  classical
  let n := Fintype.card W
  let d := defect eps n
  let q := quota a n
  let b := supply eps n
  have hdeg : ∀ x, (3 / 4 : ℝ) * Fintype.card W ≤ G.degree x := by
    intro x
    exact hmin.trans (by exact_mod_cast G.minDegree_le_degree x)
  have hroot : ∀ x, incidentLoad (internal p G.edgeFinset) x ≤ d := by
    intro x
    exact Nat.le_floor (hint x)
  have hneigh : ∀ x, ((CleanupSupplyStage140.internalNeighbours G p x).card : ℝ) ≤
      eps * Fintype.card W := by
    intro x
    rw [← internal_load_eq G p x]
    exact hint x
  have hsupply : ∀ u v k, G.Adj u v → p u = p v → k ≠ p u →
      b ≤ (RequestPackingStage140.candidates p G u v k).card := by
    intro u v k _ hp hk
    have hh := CleanupSupplyStage140.candidates_lower G p eps heps.le hdeg hneigh
      u v k hk (by rwa [← hp])
    rw [candidates_eq] at hh
    have hb : (b : ℝ) ≤ (1 / 4 - 11 * eps) * Fintype.card W :=
      Nat.floor_le (mul_nonneg (by linarith) (Nat.cast_nonneg _))
    exact_mod_cast hb.trans hh
  obtain ⟨_, _, hsmall, hbudget⟩ := hnum n (le_of_max_le_right hW)
  have hcount : (internal p G.edgeFinset).card ≤ n * d :=
    ChildBalanceStage128.card_le_of_load _ d hroot
  apply hconsume W (le_of_max_le_left hW) G p b d q hmin hdiv hroot hsupply
  · exact hbudget _ hcount
  · exact hsmall

end PartitionedTriangleAbsorption.CleanupGeometryStage140

