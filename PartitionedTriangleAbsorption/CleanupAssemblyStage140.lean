/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupConsumerStage140
public import PartitionedTriangleAbsorption.CleanupCutBalanceStage140
public import PartitionedTriangleAbsorption.RequestPackingStage140
public import PartitionedTriangleAbsorption.CutSurplusStage140

/-! # Constructing and consuming the matched cleanup

The inputs are local common-neighbour supply and numerical budgets, not a
preselected packing or quota assignment. The assignment is obtained from
ordinary divisibility and the three cut surpluses; its physical realization
then supplies exactly the residual balances consumed by Stage84.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupAssemblyStage140

open Finset OnePart AntiEdgeSelection MatchedQuotaStage140
open RequestPackingStage140 RootQuotaPackingStage124

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_balanced_cleanup (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (b d q : ℕ)
    (hdiv : IsIntDiv part1 triFam G.edgeFinset)
    (hsurplus : ∀ i : Fin 3, 3 * (cuts p G.edgeFinset i).card ≤ 2 * G.edgeFinset.card)
    (hroot : ∀ x, incidentLoad (internal p G.edgeFinset) x ≤ d)
    (hsupply : ∀ u v k, G.Adj u v → p u = p v → k ≠ p u →
      b ≤ (candidates p G u v k).card)
    (hbudget : 2 * (internal p G.edgeFinset).card + 2 * (d + 2 * q) * q < b * q) :
    ∃ Q : Finset (Sym2 V), Q ⊆ G.edgeFinset ∧
      HasDecomp part1 triFam Q ∧ DegBounded Q (2 * d + 2 * q) ∧
      (∀ u v, G.Adj u v → p u = p v → s(u, v) ∈ Q) ∧
      (edgeVec p (G.edgeFinset \ Q) 0 1 + edgeVec p (G.edgeFinset \ Q) 2 3 =
        edgeVec p (G.edgeFinset \ Q) 0 2 + edgeVec p (G.edgeFinset \ Q) 1 3) ∧
      (edgeVec p (G.edgeFinset \ Q) 0 1 + edgeVec p (G.edgeFinset \ Q) 2 3 =
        edgeVec p (G.edgeFinset \ Q) 0 3 + edgeVec p (G.edgeFinset \ Q) 1 2) := by
  classical
  let B := internal p G.edgeFinset
  have hloop : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag :=
    fun _ he => G.not_isDiag_of_mem_edgeFinset he
  have hloopB : ∀ e ∈ B, ¬ e.IsDiag :=
    fun _ he => hloop _ (mem_filter.mp he).1
  have hdiv' := (isIntDiv_part1_iff _ hloop).mp hdiv
  obtain ⟨a, ha⟩ := exists_internal_assignment p G.edgeFinset hloop hdiv' hsurplus
  let u : B → V := edgeLeft B
  let v : B → V := edgeRight B
  let k : B → Fin 4 := fun e => partner (a e) (p (u e))
  have hbase : ∀ e : B, G.Adj (u e) (v e) := by
    intro e
    change s(u e, v e) ∈ G.edgeSet
    apply G.mem_edgeFinset.mp
    rw [show s(u e, v e) = e.val from edge_rebuild B e]
    exact (mem_filter.mp e.property).1
  have hp : ∀ e : B, p (u e) = p (v e) :=
    internal_endpoints_same p G.edgeFinset
  have hk : ∀ e : B, k e ≠ p (u e) := fun e => partner_ne (a e) (p (u e))
  have hr : ∀ x, rootLoad univ u v x ≤ d := by
    intro x
    rw [rootLoad_edges B hloopB]
    exact hroot x
  have hb : 2 * (univ : Finset B).card + 2 * (d + 2 * q) * q < b * q := by
    simpa only [card_univ, Fintype.card_coe] using hbudget
  obtain ⟨w, hw, hdis, _, hQsub, hQdec, hQbase, hQdeg⟩ :=
    exists_cleanup p G u v k univ d q b
      (fun e _ => hbase e) (fun e _ => hp e) (fun e _ => hk e)
      (oriented_injective B).injOn hr
      (fun e _ => hsupply (u e) (v e) (k e) (hbase e) (hp e) (hk e)) hb
  let Q := packingEdges univ u v w
  let quota : Fin 3 → ℕ := fun i => ((univ : Finset B).filter fun e => a e = i).card
  have hquota : ∀ i, 6 * quota i + 3 * (cuts p G.edgeFinset i).card =
      2 * G.edgeFinset.card := by
    intro i
    simpa only [quota, Fintype.card_subtype] using ha i
  have hqle : ∀ i, quota i ≤ (univ : Finset B).card :=
    fun i => card_le_card (filter_subset _ _)
  have hQcuts : ∀ i, (cuts p Q i).card = 2 * ((univ : Finset B).card - quota i) := by
    intro i
    exact cuts_packing p univ u v w a (fun e _ => (hbase e).ne)
      (fun e _ => hp e) (fun e he => (hw e he).2.2) hdis i
  have heq := residual_cuts_equal p G.edgeFinset Q hQsub
    (univ : Finset B).card quota hquota hqle hQcuts
  have hbal := CleanupCutBalanceStage140.balances_of_equal_cuts p (G.edgeFinset \ Q)
    (heq 0 1) (heq 0 2)
  refine ⟨Q, hQsub, hQdec, hQdeg, ?_, hbal⟩
  intro x y hxy hp'
  have he : s(x, y) ∈ B := mem_filter.mpr ⟨G.mem_edgeFinset.mpr hxy, by
    simpa only [Sym2.map_mk, Sym2.mk_isDiag_iff] using hp'⟩
  let e : B := ⟨s(x, y), he⟩
  have h := hQbase e (mem_univ e)
  rwa [show s(u e, v e) = s(x, y) from edge_rebuild B e] at h

/-- All combinatorial choices are constructed internally from supply and
budgets. The remaining inputs can be discharged by geometric degree estimates. -/
theorem decomposition_of_uniform_supply :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 / 16 ∧ ∃ N : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W], N ≤ Fintype.card W →
        ∀ (G : SimpleGraph W) [DecidableRel G.Adj] (p : W → Fin 4) (b d q : ℕ),
          (3 / 4 : ℝ) * Fintype.card W ≤ (G.minDegree : ℝ) →
          IsIntDiv part1 triFam G.edgeFinset →
          (∀ x, incidentLoad (internal p G.edgeFinset) x ≤ d) →
          (∀ u v k, G.Adj u v → p u = p v → k ≠ p u →
            b ≤ (candidates p G u v k).card) →
          2 * (internal p G.edgeFinset).card + 2 * (d + 2 * q) * q < b * q →
          (2 * (d : ℝ) + 2 * q ≤ eps * Fintype.card W) →
          HasDecomp part1 triFam G.edgeFinset := by
  obtain ⟨eps, heps, heps1, N, hN⟩ := CleanupConsumerStage140.decomposition_of_cleanup
  refine ⟨eps, heps, heps1, N, ?_⟩
  intro W _ _ hW G _ p b d q hmin hdiv hroot hsupply hbudget hsmall
  have hsurplus : ∀ i : Fin 3, 3 * (cuts p G.edgeFinset i).card ≤
      2 * G.edgeFinset.card := CutSurplusStage140.surplus_of_real_degree p G
        (fun v => hmin.trans (by exact_mod_cast G.minDegree_le_degree v))
  obtain ⟨Q, hQsub, hQdec, hQdeg, hcover, hbal1, hbal2⟩ :=
    exists_balanced_cleanup G p b d q hdiv hsurplus hroot hsupply hbudget
  exact hN W hW G p Q hmin hdiv hQsub hQdec
    (fun x => (hQdeg x).trans hsmall) hcover hbal1 hbal2

end PartitionedTriangleAbsorption.CleanupAssemblyStage140
