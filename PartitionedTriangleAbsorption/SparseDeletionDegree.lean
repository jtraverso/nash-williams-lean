/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingRestriction

/-! # Physical degree control after deleting the absorber and reserve

The bounds count actual removed incident edges. The union estimate allows
overlap; disjointness is needed later for absorption, not for this estimate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SparseDeletionDegree

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem degBounded_union {A B : Finset (Sym2 V)} {a b : ℝ}
    (hA : DegBounded A a) (hB : DegBounded B b) : DegBounded (A ∪ B) (a + b) := by
  intro v
  rw [filter_union]
  have hc := card_union_le (A.filter (fun e => v ∈ e)) (B.filter (fun e => v ∈ e))
  have hr : (((A.filter (fun e => v ∈ e)) ∪ (B.filter (fun e => v ∈ e))).card : ℝ) ≤
      ((A.filter (fun e => v ∈ e)).card : ℝ) + (B.filter (fun e => v ∈ e)).card := by
    exact_mod_cast hc
  exact hr.trans (add_le_add (hA v) (hB v))

theorem degree_le_delete_add (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) {d : ℝ} (hB : DegBounded B d) (v : V) :
    (G.degree v : ℝ) ≤ (G.deleteEdges (B : Set (Sym2 V))).degree v + d := by
  classical
  let J := G.deleteEdges (B : Set (Sym2 V))
  let lost := univ.filter (fun w => s(v, w) ∈ B)
  have hsub : G.neighborFinset v ⊆ J.neighborFinset v ∪ lost := by
    intro w hw
    by_cases he : s(v, w) ∈ B
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, he⟩)
    · apply mem_union_left
      rw [SimpleGraph.mem_neighborFinset] at hw ⊢
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨hw, he⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hd := PackingRestriction.endpoint_neighbor_count B v
  have hr : (G.degree v : ℝ) ≤ (J.degree v : ℝ) + lost.card := by
    exact_mod_cast hc
  have hl : (lost.card : ℝ) ≤ (B.filter (fun e => v ∈ e)).card := by
    exact_mod_cast hd
  exact hr.trans (add_le_add le_rfl (hl.trans (hB v)))

theorem minDegree_delete (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (a b : ℝ)
    (hmin : ∀ v, a * Fintype.card V ≤ G.degree v)
    (hB : DegBounded B (b * Fintype.card V)) :
    ∀ v, (a - b) * Fintype.card V ≤ (G.deleteEdges (B : Set (Sym2 V))).degree v := by
  intro v
  have hd := degree_le_delete_add G B hB v
  have hv := hmin v
  nlinarith

end PartitionedTriangleAbsorption.SparseDeletionDegree
