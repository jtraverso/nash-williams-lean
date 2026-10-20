/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupSupplyStage140
public import Mathlib.Tactic

/-! # Two external classes with many common neighbours

This formalizes the quantitative contradiction in Claim 12.8.5 (page 113).
The printed definition of L(e) contains an unbound k. Here the list is defined
explicitly by the common-neighbour count in each single destination class.
No assertion about a list of paired colours is made.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CommonClassSupply

open Finset ClassRepresentativesStage65 CleanupSupplyStage140

variable {V : Type*} [Fintype V] [DecidableEq V]

def classNeighbours (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) (j : Fin 4) : Finset V :=
  G.neighborFinset v ∩ classSet p j

noncomputable def destinationList (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (t : ℝ) : Finset (Fin 4) :=
  univ.filter fun j => j ≠ p u ∧ t * Fintype.card V ≤ (candidates G p u v j).card

theorem degree_partition (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (v : V) :
    ∑ j : Fin 4, (classNeighbours G p v j).card = G.degree v := by
  classical
  have he (j : Fin 4) : classNeighbours G p v j =
      (G.neighborFinset v).filter (fun w => p w = j) := by
    ext w
    simp [classNeighbours, classSet]
  simp_rw [he]
  rw [sum_card_fiberwise_eq_card_filter]
  simp

theorem common_neighbour_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (j : Fin 4) :
    (classNeighbours G p u j).card + (classNeighbours G p v j).card ≤
      (classSet p j).card + (candidates G p u v j).card := by
  have h := card_union_add_card_inter (classNeighbours G p u j) (classNeighbours G p v j)
  have hs : classNeighbours G p u j ∪ classNeighbours G p v j ⊆ classSet p j := by
    intro w hw
    rcases mem_union.mp hw with hu | hv
    · exact (mem_inter.mp hu).2
    · exact (mem_inter.mp hv).2
  have hi : classNeighbours G p u j ∩ classNeighbours G p v j = candidates G p u v j := by
    ext w
    simp only [classNeighbours, candidates, mem_inter]
    tauto
  rw [hi] at h
  have := card_le_card hs
  omega

theorem fourth_class {i a b : Fin 4} (hia : i ≠ a) (hib : i ≠ b) (hab : a ≠ b) :
    ∃ c : Fin 4, (univ : Finset (Fin 4)) = {i, a, b, c} ∧
      i ≠ c ∧ a ≠ c ∧ b ≠ c := by
  revert i a b
  decide

/-- The numerical heart of the argument; all margins are explicit. -/
theorem two_small_classes_impossible (n eps t du dv : ℝ) (d : Fin 4 → ℝ)
    (hn : 0 < n) (hmargin : 1 + 6 * eps + 2 * t < 9 / 8)
    (hu : 3 / 4 * n ≤ du) (hv : 3 / 4 * n ≤ dv)
    (hsum : ∑ j, d j = du + dv)
    (i a b : Fin 4) (hia : i ≠ a) (hib : i ≠ b) (hab : a ≠ b)
    (hi : d i ≤ (du + dv) / 4 + 2 * eps * n)
    (ha : d a ≤ (1 / 4 + eps + t) * n)
    (hb : d b ≤ (1 / 4 + eps + t) * n)
    (hother : ∀ j, d j ≤ 2 * (1 / 4 + eps) * n) : False := by
  obtain ⟨c, hc, hic, hac, hbc⟩ := fourth_class hia hib hab
  have hs : d i + d a + d b + d c = du + dv := by
    rw [hc] at hsum
    simpa [hia, hib, hic, hab, hac, hbc, add_assoc] using hsum
  have hm : (1 + 6 * eps + 2 * t) * n < (9 / 8) * n :=
    mul_lt_mul_of_pos_right hmargin hn
  nlinarith [hother c]

/-- At least two external destination classes each contain t n common neighbours.
Only u and v need the internal-degree bound. Their adjacency is not required. -/
theorem destinationList_card_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (eps t : ℝ)
    (hn : 0 < Fintype.card V) (hmargin : 1 + 6 * eps + 2 * t < 9 / 8)
    (hsize : ∀ j, ((classSet p j).card : ℝ) ≤ (1 / 4 + eps) * Fintype.card V)
    (hu : (3 / 4 : ℝ) * Fintype.card V ≤ G.degree u)
    (hv : (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hp : p u = p v)
    (hiu : ((internalNeighbours G p u).card : ℝ) ≤ G.degree u / 4 + eps * Fintype.card V)
    (hiv : ((internalNeighbours G p v).card : ℝ) ≤ G.degree v / 4 + eps * Fintype.card V) :
    2 ≤ (destinationList G p u v t).card := by
  classical
  by_contra h
  have hlist : (destinationList G p u v t).card ≤ 1 := by omega
  let excluded := destinationList G p u v t ∪ {p u}
  have hex : excluded.card ≤ 2 := by
    have := card_union_le (destinationList G p u v t) {p u}
    simp only [card_singleton] at this
    dsimp [excluded]
    omega
  have hbad : 1 < excludedᶜ.card := by
    rw [card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp hbad
  have bad (j : Fin 4) (hj : j ∈ excludedᶜ) :
      j ≠ p u ∧ ((candidates G p u v j).card : ℝ) < t * Fintype.card V := by
    have hx : j ∉ excluded := mem_compl.mp hj
    have hji : j ≠ p u := by
      intro he
      apply hx
      exact mem_union_right _ (mem_singleton.mpr he)
    have hl : j ∉ destinationList G p u v t := fun h => hx (mem_union_left _ h)
    refine ⟨hji, ?_⟩
    apply lt_of_not_ge
    intro hh
    apply hl
    exact mem_filter.mpr ⟨mem_univ _, hji, hh⟩
  obtain ⟨hai, hca⟩ := bad a ha
  obtain ⟨hbi, hcb⟩ := bad b hb
  let d : Fin 4 → ℝ := fun j => (classNeighbours G p u j).card + (classNeighbours G p v j).card
  have hsum : ∑ j, d j = (G.degree u : ℝ) + G.degree v := by
    simp only [d, sum_add_distrib]
    exact_mod_cast congrArg₂ (· + ·) (degree_partition G p u) (degree_partition G p v)
  have hi : d (p u) ≤ ((G.degree u : ℝ) + G.degree v) / 4 + 2 * eps * Fintype.card V := by
    have he : classNeighbours G p v (p u) = internalNeighbours G p v := by
      rw [hp]; rfl
    change (internalNeighbours G p u).card + ((classNeighbours G p v (p u)).card : ℝ) ≤ _
    rw [he]
    linarith
  have small (j : Fin 4) (hj : ((candidates G p u v j).card : ℝ) < t * Fintype.card V) :
      d j ≤ (1 / 4 + eps + t) * Fintype.card V := by
    have hb : d j ≤ (classSet p j).card + ((candidates G p u v j).card : ℝ) := by
      dsimp [d]
      exact_mod_cast common_neighbour_budget G p u v j
    nlinarith [hsize j]
  have other (j : Fin 4) : d j ≤ 2 * (1 / 4 + eps) * Fintype.card V := by
    have h1 : ((classNeighbours G p u j).card : ℝ) ≤ (classSet p j).card := by
      exact_mod_cast card_le_card (show classNeighbours G p u j ⊆ classSet p j from
        inter_subset_right)
    have h2 : ((classNeighbours G p v j).card : ℝ) ≤ (classSet p j).card := by
      exact_mod_cast card_le_card (show classNeighbours G p v j ⊆ classSet p j from
        inter_subset_right)
    dsimp [d]
    nlinarith [hsize j]
  exact two_small_classes_impossible (Fintype.card V) eps t (G.degree u) (G.degree v) d
    (by exact_mod_cast hn) hmargin hu hv hsum (p u) a b hai.symm hbi.symm hab hi
    (small a hca) (small b hcb) other

/-- The paper's 0.05 n threshold, with eps = 2 sqrt(alpha) if desired.
The margin eps < 1/240 is sufficient without an asymptotic hierarchy. -/
theorem paper_threshold_card_ge_two (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (eps : ℝ)
    (hn : 0 < Fintype.card V) (heps : eps < 1 / 240)
    (hsize : ∀ j, ((classSet p j).card : ℝ) ≤ (1 / 4 + eps) * Fintype.card V)
    (hmin : (3 / 4 : ℝ) * Fintype.card V ≤ G.minDegree)
    (hp : p u = p v)
    (hiu : ((internalNeighbours G p u).card : ℝ) ≤ G.degree u / 4 + eps * Fintype.card V)
    (hiv : ((internalNeighbours G p v).card : ℝ) ≤ G.degree v / 4 + eps * Fintype.card V) :
    2 ≤ (destinationList G p u v (1 / 20)).card := by
  apply destinationList_card_ge_two G p u v eps (1 / 20) hn (by linarith) hsize
    _ _ hp hiu hiv
  · exact hmin.trans (by exact_mod_cast G.minDegree_le_degree u)
  · exact hmin.trans (by exact_mod_cast G.minDegree_le_degree v)

/-- Extract two distinct classes and their physical common-neighbour supplies. -/
theorem exists_two_destination_classes (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (u v : V) (eps : ℝ)
    (hn : 0 < Fintype.card V) (heps : eps < 1 / 240)
    (hsize : ∀ j, ((classSet p j).card : ℝ) ≤ (1 / 4 + eps) * Fintype.card V)
    (hmin : (3 / 4 : ℝ) * Fintype.card V ≤ G.minDegree)
    (hp : p u = p v)
    (hiu : ((internalNeighbours G p u).card : ℝ) ≤ G.degree u / 4 + eps * Fintype.card V)
    (hiv : ((internalNeighbours G p v).card : ℝ) ≤ G.degree v / 4 + eps * Fintype.card V) :
    ∃ j k : Fin 4, j ≠ k ∧ j ≠ p u ∧ k ≠ p u ∧
      (Fintype.card V : ℝ) / 20 ≤ (candidates G p u v j).card ∧
      (Fintype.card V : ℝ) / 20 ≤ (candidates G p u v k).card := by
  classical
  have hc := paper_threshold_card_ge_two G p u v eps hn heps hsize hmin hp hiu hiv
  obtain ⟨j, hj, k, hk, hjk⟩ := one_lt_card.mp
    (by omega : 1 < (destinationList G p u v (1 / 20)).card)
  have hj' := (mem_filter.mp hj).2
  have hk' := (mem_filter.mp hk).2
  refine ⟨j, k, hjk, hj'.1, hk'.1, ?_, ?_⟩
  · simpa only [div_eq_mul_inv, one_mul, mul_comm] using hj'.2
  · simpa only [div_eq_mul_inv, one_mul, mul_comm] using hk'.2

end PartitionedTriangleAbsorption.CommonClassSupply
