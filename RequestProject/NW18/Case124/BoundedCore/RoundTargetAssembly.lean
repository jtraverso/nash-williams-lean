/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.BoundedCore.ApexTargets

@[expose] public section

/-! Assemble target budgets from the single physical leftover degree bound.
No hypothesis on the final targets or on a completed round is introduced. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset PartitionedTriangleAbsorption

theorem round_target_degree_budgets {V : Type*} [DecidableEq V]
    (W X : Finset V) (available L Res Ep : Finset (Sym2 V)) (D : ℕ)
    (hL : ∀ e ∈ L, ∀ v ∈ e, v ∉ W)
    (hLsub : L ⊆ available \ (Res ∪ Ep))
    (hRes : ∀ e ∈ Res, ∃ u, u ∉ W ∧ ∃ z ∈ W, e = s(u, z))
    (havailable : Res ⊆ available) (hEp : Disjoint Res Ep)
    (T : Finset (Finset V)) (hT : ∀ t ∈ T, t.card = 3)
    (hdisj : (T : Set (Finset V)).PairwiseDisjoint triEdges)
    (hsub : T.biUnion triEdges ⊆ L ∪ Res)
    (hD : ∀ v, ((available \ (Res ∪ Ep)).filter (fun e => v ∈ e)).card ≤ D) :
    (∀ x, x ∉ W →
      ((W.filter (fun z => s(x, z) ∈ Res)) \
        (W.filter (fun z => s(x, z) ∈ available \ (Ep ∪ T.biUnion triEdges)))).card ≤ D ∧
      ((W.filter (fun z => s(x, z) ∈ available \ (Ep ∪ T.biUnion triEdges))) \
        (W.filter (fun z => s(x, z) ∈ Res))).card ≤ D) ∧
    (∀ v, (X.filter (fun x => s(x, v) ∈ available \ (Ep ∪ T.biUnion triEdges))).card ≤
      (X.filter (fun x => s(x, v) ∈ Res)).card + D) := by
  classical
  constructor
  · intro x hx
    constructor
    · exact (apex_neighbour_reserve_loss W available L Res Ep hL hRes havailable hEp
        T hT hdisj hsub x hx).trans
        ((card_le_card (filter_subset_filter _ hLsub)).trans (hD x))
    · exact (unreserved_target_degree W available Res Ep (T.biUnion triEdges) x).trans (hD x)
  · intro v
    exact (target_inverse_load_degree X available Res Ep (T.biUnion triEdges) v).trans
      (Nat.add_le_add_left (hD v) _)

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.round_target_degree_budgets
