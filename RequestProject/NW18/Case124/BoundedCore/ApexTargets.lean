/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.BoundedCore.ApexCharge

/-! Root targets after physical apex coverage. Loss of sampled reserve and
addition of unreserved targets are both charged to the actual nibble leftover. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [DecidableEq V]

theorem apex_neighbour_reserve_loss (W : Finset V)
    (available L Res Ep : Finset (Sym2 V))
    (hL : ∀ e ∈ L, ∀ v ∈ e, v ∉ W)
    (hRes : ∀ e ∈ Res, ∃ u, u ∉ W ∧ ∃ z ∈ W, e = s(u, z))
    (havailable : Res ⊆ available) (hEp : Disjoint Res Ep)
    (T : Finset (Finset V)) (hT : ∀ t ∈ T, t.card = 3)
    (hdisj : (T : Set (Finset V)).PairwiseDisjoint triEdges)
    (hsub : T.biUnion triEdges ⊆ L ∪ Res) (x : V) (hx : x ∉ W) :
    ((W.filter (fun z => s(x, z) ∈ Res)) \
      (W.filter (fun z => s(x, z) ∈ available \ (Ep ∪ T.biUnion triEdges)))).card ≤
        (L.filter (fun e => x ∈ e)).card := by
  classical
  let lost := Res \ (available \ (Ep ∪ T.biUnion triEdges))
  have heq : (W.filter (fun z => s(x, z) ∈ Res)) \
      (W.filter (fun z => s(x, z) ∈ available \ (Ep ∪ T.biUnion triEdges))) =
      W.filter (fun z => s(x, z) ∈ lost) := by
    ext z
    simp only [lost, mem_sdiff, mem_filter]
    tauto
  rw [heq, radial_incidence_card W lost
    (fun e he => hRes e (mem_sdiff.mp he).1) x hx]
  exact reserve_loss_after_apex W available L Res Ep hL hRes havailable hEp T hT
    hdisj hsub x hx

/-- Unreserved targets are part of the actual protected leftover, even when
the apex cover also removes some of them. -/
theorem unreserved_target_degree (W : Finset V)
    (available Res Ep Ta : Finset (Sym2 V)) (x : V) :
    ((W.filter (fun z => s(x, z) ∈ available \ (Ep ∪ Ta))) \
      (W.filter (fun z => s(x, z) ∈ Res))).card ≤
        (((available \ (Res ∪ Ep)).filter (fun e => x ∈ e)).card) := by
  classical
  refine card_le_card_of_injOn (fun z => s(x, z)) ?_ ?_
  · intro z hz
    obtain ⟨hzF, hzR⟩ := mem_sdiff.mp hz
    obtain ⟨hzW, hzA⟩ := mem_filter.mp hzF
    have hzRes : s(x, z) ∉ Res := fun h => hzR (mem_filter.mpr ⟨hzW, h⟩)
    obtain ⟨hzE, hzNot⟩ := mem_sdiff.mp hzA
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨hzE, ?_⟩, by simp⟩
    intro he
    rcases mem_union.mp he with h | h
    · exact hzRes h
    · exact hzNot (mem_union_left _ h)
  · intro z _ z' _ heq
    exact Sym2.congr_right.mp heq

/-- Inverse load needs its own per-vertex charge; rootwise losses alone do not
bound it. New incidences at `v` inject into leftover edges incident to `v`. -/
theorem target_inverse_load_degree (X : Finset V)
    (available Res Ep Ta : Finset (Sym2 V)) (v : V) :
    (X.filter (fun x => s(x, v) ∈ available \ (Ep ∪ Ta))).card ≤
      (X.filter (fun x => s(x, v) ∈ Res)).card +
        (((available \ (Res ∪ Ep)).filter (fun e => v ∈ e)).card) := by
  classical
  let targets := X.filter (fun x => s(x, v) ∈ available \ (Ep ∪ Ta))
  let reserved := X.filter (fun x => s(x, v) ∈ Res)
  have hnew : (targets \ reserved).card ≤
      (((available \ (Res ∪ Ep)).filter (fun e => v ∈ e)).card) := by
    refine card_le_card_of_injOn (fun x => s(x, v)) ?_ ?_
    · intro x hx
      obtain ⟨hxT, hxR⟩ := mem_sdiff.mp hx
      obtain ⟨hxX, hxA⟩ := mem_filter.mp hxT
      have hxRes : s(x, v) ∉ Res := fun h => hxR (mem_filter.mpr ⟨hxX, h⟩)
      obtain ⟨hxE, hxNot⟩ := mem_sdiff.mp hxA
      refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨hxE, ?_⟩, by simp⟩
      intro he
      rcases mem_union.mp he with h | h
      · exact hxRes h
      · exact hxNot (mem_union_left _ h)
    · intro x _ x' _ heq
      exact Sym2.congr_left.mp heq
  have hcard := card_le_card_sdiff_add_card (s := targets) (t := reserved)
  dsimp only [targets, reserved] at hcard hnew
  omega

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.apex_neighbour_reserve_loss
#print axioms NashWilliams18.Case124.BoundedCore.unreserved_target_degree
#print axioms NashWilliams18.Case124.BoundedCore.target_inverse_load_degree
