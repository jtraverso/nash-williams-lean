/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.Geometry
import Mathlib.Tactic.Linarith

/-! # Elementary bounds in the actual two-part host -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε : ℝ}

theorem other0_ne (i : Fin 2) : other0 i ≠ i := by
  revert i
  decide

theorem eq_or_eq_other0 (i j : Fin 2) : j = i ∨ j = other0 i := by
  revert i j
  decide

theorem partSet_card_add (p : V → Fin 2) (i : Fin 2) :
    (partSet p i).card + (partSet p (other0 i)).card = Fintype.card V := by
  have hd : Disjoint (partSet p i) (partSet p (other0 i)) := by
    apply disjoint_left.mpr
    intro v hi hj
    exact other0_ne i ((mem_partSet.mp hj).symm.trans (mem_partSet.mp hi))
  have hu : partSet p i ∪ partSet p (other0 i) = univ := by
    ext v
    simp only [mem_union, mem_partSet, mem_univ, iff_true]
    exact eq_or_eq_other0 i (p v)
  rw [← card_union_of_disjoint hd, hu, card_univ]

theorem HostHyp.part_upper (h : HostHyp p G α ε) (i : Fin 2) :
    ((partSet p i).card : ℝ) ≤ (1 + ε) * Fintype.card V / 2 := by
  have hc : ((partSet p i).card : ℝ) + (partSet p (other0 i)).card =
      Fintype.card V := by exact_mod_cast partSet_card_add p i
  have hl := h.part_size (other0 i)
  nlinarith

theorem HostHyp.part_present (h : HostHyp p G α ε) (hε : ε ≤ 1 / 2)
    (hn : 0 < Fintype.card V) (i : Fin 2) : ∃ v, p v = i := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hsize := h.part_size i
  have hc : 0 < (partSet p i).card := by
    have hcR : (0 : ℝ) < (partSet p i).card := by nlinarith
    exact_mod_cast hcR
  obtain ⟨v, hv⟩ := card_pos.mp hc
  exact ⟨v, mem_partSet.mp hv⟩

theorem HostHyp.cross_to_lower (h : HostHyp p G α ε) (v : V) (k : Fin 2)
    (hk : p v ≠ k) :
    (1 / 2 - ε) * Fintype.card V ≤ (partDeg p G k v : ℝ) := by
  have heq : k = other0 (p v) := (eq_or_eq_other0 (p v) k).resolve_left (Ne.symm hk)
  rw [heq]
  exact h.cross_lower v

theorem HostHyp.degree_to_lower (h : HostHyp p G α ε) (v : V) (k : Fin 2) :
    (1 / 4 - ε) * Fintype.card V ≤ (partDeg p G k v : ℝ) := by
  by_cases hk : k = p v
  · simpa only [hk] using h.internal_lower v
  · have hc := h.cross_to_lower v k (Ne.symm hk)
    have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    nlinarith

theorem commonPart_card_budget (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : Fin 2) (u v : V) :
    partDeg p G k u + partDeg p G k v ≤
      (partSet p k).card + (commonPart p G k u v).card := by
  have hsub : partNbrs p G k u ∪ partNbrs p G k v ⊆ partSet p k := by
    intro w hw
    rcases mem_union.mp hw with hu | hv
    · exact mem_partSet.mpr (mem_partNbrs.mp hu).1
    · exact mem_partSet.mpr (mem_partNbrs.mp hv).1
  have hc := card_le_card hsub
  have heq := card_union_add_card_inter (partNbrs p G k u) (partNbrs p G k v)
  rw [commonPart_same]
  unfold partDeg
  omega

/-- Every permitted completion uses at least one crossing spoke. -/
theorem completion_has_crossing_spoke (i j k : Fin 2)
    (h : ({i, j, k} : Multiset (Fin 2)) ∈ F0) : i ≠ k ∨ j ≠ k := by
  revert i j k
  decide

/-- Uniform anti-edgefulness follows from the original degree hypotheses.
The nonextremality field is not used in this elementary estimate. -/
theorem HostHyp.antiEdgeful (h : HostHyp p G α ε) (hε : ε ≤ 1 / 20) :
    AntiEdgeful p F0 G (1 / 8) := by
  intro τ hτ i j k hijk u v huv hui hvj
  have htype : ({i, j, k} : Multiset (Fin 2)) ∈ F0 := hijk ▸ hτ
  have hcross := completion_has_crossing_spoke i j k htype
  have hu := h.degree_to_lower u k
  have hv := h.degree_to_lower v k
  have hsum : (3 / 4 - 2 * ε) * Fintype.card V ≤
      (partDeg p G k u : ℝ) + partDeg p G k v := by
    rcases hcross with hi | hj
    · have hc := h.cross_to_lower u k (by simpa only [hui] using hi)
      nlinarith
    · have hc := h.cross_to_lower v k (by simpa only [hvj] using hj)
      nlinarith
  have hb : (partDeg p G k u : ℝ) + partDeg p G k v ≤
      (partSet p k).card + (commonPart p G k u v).card := by
    exact_mod_cast commonPart_card_budget p G k u v
  have hp := h.part_upper k
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hcn : (1 / 8 : ℝ) * Fintype.card V ≤ (commonPart p G k u v).card := by
    nlinarith
  have hset : univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k) =
      commonPart p G k u v := by
    ext w
    simp only [mem_filter, mem_univ, true_and, mem_commonPart]
    constructor
    · rintro ⟨huw, hwv, hw⟩
      exact ⟨hw, huw, (G.adj_comm _ _).mp hwv⟩
    · rintro ⟨hw, huw, hvw⟩
      exact ⟨huw, (G.adj_comm _ _).mp hvw, hw⟩
  rw [hset]
  exact hcn

#print axioms HostHyp.part_upper
#print axioms HostHyp.part_present
#print axioms HostHyp.antiEdgeful

end PartitionedTriangleAbsorption.BlowupB.F0Direct
