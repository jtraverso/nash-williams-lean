/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Tauto
public import RequestProject.NW18.Case124.BoundedCore.RoundTargets

@[expose] public section

/-! Physical charging at exterior roots. The conclusion uses only the actual
support of an edge-disjoint triangle family, not a global bound on apex visits. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [DecidableEq V]

private lemma triangle_edges {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    triEdges ({a, b, c} : Finset V) = {s(a, b), s(a, c), s(b, c)} := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    simp only [triEdges, mem_filter, mk_mem_sym2_iff, Sym2.mk_isDiag_iff,
      mem_insert, mem_singleton, Sym2.eq_iff]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> simp_all
    · rintro (h | h | h) <;> rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [eq_comm]

/-- Within one triangle, a reserve radial at an exterior root is charged to
the unique exterior edge incident to that root. -/
theorem triangle_reserve_charge (W : Finset V) (L Res : Finset (Sym2 V))
    (hL : ∀ e ∈ L, ∀ v ∈ e, v ∉ W)
    (hRes : ∀ e ∈ Res, ∃ u, u ∉ W ∧ ∃ z ∈ W, e = s(u, z))
    (t : Finset V) (ht : t.card = 3) (hsub : triEdges t ⊆ L ∪ Res)
    (x : V) (hx : x ∉ W) :
    (((triEdges t ∩ Res).filter (fun e => x ∈ e)).card) ≤
      (((triEdges t ∩ L).filter (fun e => x ∈ e)).card) := by
  classical
  by_cases hempty : (triEdges t ∩ Res).filter (fun e => x ∈ e) = ∅
  · simp [hempty]
  obtain ⟨e, he⟩ := nonempty_iff_ne_empty.mpr hempty
  obtain ⟨heI, hxe⟩ := mem_filter.mp he
  obtain ⟨het, heR⟩ := mem_inter.mp heI
  obtain ⟨u, hu, z, hz, rfl⟩ := hRes e heR
  have hxu : x = u := by
    rcases Sym2.mem_iff.mp hxe with h | h
    · exact h
    · exact False.elim (hx (h ▸ hz))
  subst u
  have hxz : x ≠ z := fun h => hx (h ▸ hz)
  have hxt : x ∈ t := (mem_sym2_iff.mp (mem_filter.mp het).1) x (by simp)
  have hzt : z ∈ t := (mem_sym2_iff.mp (mem_filter.mp het).1) z (by simp)
  obtain ⟨y, hyt, hypair⟩ := exists_mem_notMem_of_card_lt_card
    (show ({x, z} : Finset V).card < t.card by simp [hxz, ht])
  have hxy : x ≠ y := fun h => hypair (by simp [← h])
  have hzy : z ≠ y := fun h => hypair (by simp [← h])
  have hteq : t = {x, z, y} := (eq_of_subset_of_card_le
    (by intro v hv; simp only [mem_insert, mem_singleton] at hv
        rcases hv with rfl | rfl | rfl <;> assumption)
    (by simp [ht, hxz, hxy, hzy])).symm
  have hzyE : s(z, y) ∈ triEdges t := by simp [hteq, triangle_edges hxz hxy hzy]
  have hy : y ∉ W := by
    rcases mem_union.mp (hsub hzyE) with h | h
    · exact hL _ h y (by simp)
    · obtain ⟨a, ha, b, hb, heq⟩ := hRes _ h
      rcases Sym2.eq_iff.mp heq with ⟨hza, hyb⟩ | ⟨hzb, hya⟩
      · exact False.elim (ha (hza ▸ hz))
      · exact hya ▸ ha
  have hxyE : s(x, y) ∈ triEdges t := by simp [hteq, triangle_edges hxz hxy hzy]
  have hxyR : s(x, y) ∉ Res := by
    intro h
    obtain ⟨a, ha, b, hb, heq⟩ := hRes _ h
    rcases Sym2.eq_iff.mp heq with ⟨_, hyb⟩ | ⟨hxb, _⟩
    · exact hy (hyb ▸ hb)
    · exact hx (hxb ▸ hb)
  have hxyL : s(x, y) ∈ L := (mem_union.mp (hsub hxyE)).resolve_right hxyR
  have hxzL : s(x, z) ∉ L := fun h => hL _ h z (by simp) hz
  have hleft : (triEdges t ∩ Res).filter (fun e => x ∈ e) = {s(x, z)} := by
    ext f
    simp only [hteq, triangle_edges hxz hxy hzy, mem_filter, mem_inter,
      mem_insert, mem_singleton]
    constructor
    · rintro ⟨⟨hf, hfR⟩, hxf⟩
      rcases hf with rfl | rfl | rfl
      · rfl
      · exact False.elim (hxyR hfR)
      · simp [Sym2.mem_iff, hxz, hxy] at hxf
    · rintro rfl
      exact ⟨⟨Or.inl rfl, heR⟩, by simp⟩
  have hright : s(x, y) ∈ (triEdges t ∩ L).filter (fun e => x ∈ e) :=
    mem_filter.mpr ⟨mem_inter.mpr ⟨hxyE, hxyL⟩, by simp⟩
  rw [hleft, card_singleton]
  exact card_pos.mpr ⟨_, hright⟩

/-- The radial reserve consumed at a fixed exterior root is at most the
leftover degree there. Edge-disjointness makes the individual charges disjoint. -/
theorem apex_reserve_charge (W : Finset V) (L Res : Finset (Sym2 V))
    (hL : ∀ e ∈ L, ∀ v ∈ e, v ∉ W)
    (hRes : ∀ e ∈ Res, ∃ u, u ∉ W ∧ ∃ z ∈ W, e = s(u, z))
    (T : Finset (Finset V)) (hT : ∀ t ∈ T, t.card = 3)
    (hdisj : (T : Set (Finset V)).PairwiseDisjoint triEdges)
    (hsub : T.biUnion triEdges ⊆ L ∪ Res) (x : V) (hx : x ∉ W) :
    ((((T.biUnion triEdges) ∩ Res).filter (fun e => x ∈ e)).card) ≤
      ((L.filter (fun e => x ∈ e)).card) := by
  classical
  have hcard (E : Finset (Sym2 V)) :
      ((((T.biUnion triEdges) ∩ E).filter (fun e => x ∈ e)).card) =
        ∑ t ∈ T, (((triEdges t ∩ E).filter (fun e => x ∈ e)).card) := by
    rw [biUnion_inter, filter_biUnion]
    exact card_biUnion (fun s hs t ht hst => (hdisj hs ht hst).mono
      ((filter_subset _ _).trans inter_subset_left)
      ((filter_subset _ _).trans inter_subset_left))
  calc
    _ = ∑ t ∈ T, (((triEdges t ∩ Res).filter (fun e => x ∈ e)).card) := hcard Res
    _ ≤ ∑ t ∈ T, (((triEdges t ∩ L).filter (fun e => x ∈ e)).card) :=
      sum_le_sum fun t ht => triangle_reserve_charge W L Res hL hRes t (hT t ht)
        (fun e he => hsub (mem_biUnion.mpr ⟨t, ht, he⟩)) x hx
    _ = ((((T.biUnion triEdges) ∩ L).filter (fun e => x ∈ e)).card) := (hcard L).symm
    _ ≤ _ := card_le_card (filter_subset_filter _ inter_subset_right)

/-- Radial incidence is counted once, on actual unordered edges. -/
theorem radial_incidence_card (W : Finset V) (Res : Finset (Sym2 V))
    (hRes : ∀ e ∈ Res, ∃ u, u ∉ W ∧ ∃ z ∈ W, e = s(u, z))
    (x : V) (hx : x ∉ W) :
    (W.filter (fun z => s(x, z) ∈ Res)).card =
      (Res.filter (fun e => x ∈ e)).card := by
  classical
  refine card_bij (fun z _ => s(x, z)) ?_ ?_ ?_
  · intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).2, by simp⟩
  · intro z _ z' _ heq
    exact Sym2.congr_right.mp heq
  · intro e he
    obtain ⟨heR, hxe⟩ := mem_filter.mp he
    obtain ⟨u, hu, z, hz, rfl⟩ := hRes e heR
    rcases Sym2.mem_iff.mp hxe with h | h
    · subst u
      exact ⟨z, mem_filter.mpr ⟨hz, heR⟩, rfl⟩
    · exact False.elim (hx (h ▸ hz))

/-- The rootwise reserve loss after nibble and apex coverage is charged solely
to the leftover degree, with no contribution from the global apex threshold. -/
theorem reserve_loss_after_apex (W : Finset V)
    (available L Res Ep : Finset (Sym2 V))
    (hL : ∀ e ∈ L, ∀ v ∈ e, v ∉ W)
    (hRes : ∀ e ∈ Res, ∃ u, u ∉ W ∧ ∃ z ∈ W, e = s(u, z))
    (havailable : Res ⊆ available) (hEp : Disjoint Res Ep)
    (T : Finset (Finset V)) (hT : ∀ t ∈ T, t.card = 3)
    (hdisj : (T : Set (Finset V)).PairwiseDisjoint triEdges)
    (hsub : T.biUnion triEdges ⊆ L ∪ Res) (x : V) (hx : x ∉ W) :
    (((Res \ (available \ (Ep ∪ T.biUnion triEdges))).filter
      (fun e => x ∈ e)).card) ≤ (L.filter (fun e => x ∈ e)).card := by
  have hloss := reserve_removed_subset available Res Ep (T.biUnion triEdges) havailable hEp
  have hsub' : Res ∩ T.biUnion triEdges = T.biUnion triEdges ∩ Res := inter_comm _ _
  rw [hsub'] at hloss
  exact (card_le_card (filter_subset_filter _ hloss)).trans
    (apex_reserve_charge W L Res hL hRes T hT hdisj hsub x hx)

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.triangle_reserve_charge
#print axioms NashWilliams18.Case124.BoundedCore.apex_reserve_charge
#print axioms NashWilliams18.Case124.BoundedCore.radial_incidence_card
#print axioms NashWilliams18.Case124.BoundedCore.reserve_loss_after_apex
