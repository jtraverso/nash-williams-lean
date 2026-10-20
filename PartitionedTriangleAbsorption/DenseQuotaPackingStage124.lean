/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootQuotaPackingStage124

/-! # Quota packing in a complete multipartite host with sparse deletions

This discharges the local common-neighbour supply of the greedy constructor.
The missing edges and the reserved edges are separate explicit inputs.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootQuotaPackingStage124

open Finset AntiEdgeSelection

variable {V I : Type*} [Fintype V] [DecidableEq V]

theorem common_supply {t : ℕ} (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (W : Finset V) (F : Finset (Sym2 V)) (f b : ℕ)
    (hF : ∀ x, incidentLoad F x ≤ f)
    (hG : ∀ x y, p x ≠ p y → s(x, y) ∉ F → G.Adj x y)
    (c : Fin t) (hpart : b + 2 * f ≤ (W.filter fun w => p w = c).card)
    (u v : V) (hu : p u ≠ c) (hv : p v ≠ c) :
    b ≤ (common p G W u v c).card := by
  let S := W.filter fun w => p w = c
  let A := S \ ((∅ : Finset V) ∪ blockedNeighbours F u ∪ blockedNeighbours F v)
  have hc := available_card_budget S ∅ F u v
  have hsub : A ⊆ common p G W u v c := by
    intro w hw
    obtain ⟨hwS, hwN⟩ := mem_sdiff.mp hw
    obtain ⟨hwW, hwc⟩ := mem_filter.mp hwS
    have heu : s(u, w) ∉ F := by
      intro h
      exact hwN (mem_union_left _ (mem_union_right _
        (mem_filter.mpr ⟨mem_univ _, h⟩)))
    have hev : s(v, w) ∉ F := by
      intro h
      exact hwN (mem_union_right _ (mem_filter.mpr ⟨mem_univ _, h⟩))
    exact mem_filter.mpr ⟨hwW, hwc,
      hG u w (by simpa [hwc] using hu) heu,
      (hG v w (by simpa [hwc] using hv) hev).symm⟩
  have hcard := card_le_card hsub
  have hfu := hF u
  have hfv := hF v
  change S.card ≤ A.card + (∅ : Finset V).card + _ + _ at hc
  simp only [card_empty, Nat.add_zero] at hc
  change b + 2 * f ≤ S.card at hpart
  omega

omit [Fintype V] in
/-- The base packing is produced, not supplied: arbitrary repeated-root slots
are realized in a complete multipartite graph minus `F`, while avoiding `B`.
This conservative budget uses full degrees, without optimizing constants. -/
theorem exists_dense_packing [Finite V] {t : ℕ} (p : V → Fin t) (G : SimpleGraph V)
    (W : Finset V) (F B : Finset (Sym2 V))
    (f d k q b : ℕ) (hF : ∀ x, incidentLoad F x ≤ f)
    (hB : ∀ x, incidentLoad B x ≤ d)
    (hG : ∀ x y, p x ≠ p y → s(x, y) ∉ F → G.Adj x y)
    (hpart : ∀ c, b + 2 * f ≤ (W.filter fun w => p w = c).card)
    (root : I → V) (left right : I → Fin t) (s : Finset I)
    (htype : ∀ i ∈ s, p (root i) ≠ left i ∧ p (root i) ≠ right i ∧
      left i ≠ right i)
    (hroot : ∀ x, auxiliaryLoad s root x ≤ k)
    (hbudget : 2 * s.card + 2 * (d + 2 * (k + q)) * q < b * q) :
    ∃ a c : I → V,
      (∀ i ∈ s, a i ∈ W ∧ c i ∈ W ∧
        G.Adj (root i) (a i) ∧ G.Adj (root i) (c i) ∧ G.Adj (a i) (c i) ∧
        p (a i) = left i ∧ p (c i) = right i ∧
        Disjoint (TypedCorrectionFamily.edges (root i) (a i) (c i)) B) ∧
      (s : Set I).PairwiseDisjoint
        (fun i => TypedCorrectionFamily.edges (root i) (a i) (c i)) ∧
      ∀ x, innerLoad s a c x ≤ q := by
  classical
  let _ := Fintype.ofFinite V
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    simp only [hb0, Nat.zero_mul, Nat.not_lt_zero] at hbudget
  have hex : ∀ c, ∃ w ∈ W, p w = c := by
    intro c
    have hc : 0 < (W.filter fun w => p w = c).card := lt_of_lt_of_le hb
      ((Nat.le_add_right b (2 * f)).trans (hpart c))
    obtain ⟨w, hw⟩ := card_pos.mp hc
    exact ⟨w, (mem_filter.mp hw).1, (mem_filter.mp hw).2⟩
  choose anchor haW hap using hex
  apply exists_packing p G W B d k q b hB root (fun i => anchor (right i))
    left right s (fun i _ => ⟨haW _, hap _⟩) hroot _ hbudget
  intro i hi v _
  constructor
  · intro hv
    exact common_supply p G W F f b hF hG (left i) (hpart _) (root i) v
      (htype i hi).1 (by rw [hv]; exact (htype i hi).2.2.symm)
  · intro hv
    exact common_supply p G W F f b hF hG (right i) (hpart _) (root i) v
      (htype i hi).2.1 (by rw [hv]; exact (htype i hi).2.2)

end PartitionedTriangleAbsorption.RootQuotaPackingStage124
