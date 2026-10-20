/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ProtectedRecutStage126
public import PartitionedTriangleAbsorption.NeighbourPoolCapacityStage114

/-! # Mutable child capacity after reserving inner bases

Category capacity is obtained from physical edges between two colour classes,
then charged only for the bases actually removed by the reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ChildCapacityStage127

open Finset CoverDownStage105 AntiEdgeSelection F3ReserveTrimStage109
open ReserveTrimStage109 ReserveRecutStage126

variable {V : Type*} [DecidableEq V]

theorem pool_partition (c : Sym2 V → Fin 3) (J R : Finset (Sym2 V)) (i : Fin 3) :
    (pool c (J \ R) i).card + (pool c (J ∩ R) i).card = (pool c J i).card := by
  have hd : pool c (J \ R) i = pool c J i \ pool c (J ∩ R) i := by
    ext e
    simp only [pool, mem_filter, mem_sdiff, mem_inter]
    tauto
  rw [hd]
  apply card_sdiff_add_card_eq_card
  intro e he
  exact mem_filter.mpr ⟨(mem_inter.mp (mem_filter.mp he).1).1, (mem_filter.mp he).2⟩

theorem capacity_after_overlap (c : Sym2 V → Fin 3) (J R : Finset (Sym2 V))
    (i : Fin 3) (H P : ℕ) (z : ℝ)
    (hJ : H ≤ (pool c J i).card)
    (hR : ((pool c (J ∩ R) i).card : ℝ) ≤ z)
    (hbudget : (P : ℝ) + z ≤ H) : P ≤ (pool c (J \ R) i).card := by
  have he := pool_partition c J R i
  have heR : ((pool c (J \ R) i).card : ℝ) +
      (pool c (J ∩ R) i).card = (pool c J i).card := by exact_mod_cast he
  have hJR : (H : ℝ) ≤ (pool c J i).card := by exact_mod_cast hJ
  have hr : (P : ℝ) ≤ (pool c (J \ R) i).card := by linarith
  exact_mod_cast hr

theorem mutable_child_capacity (p : V → Fin 4) (E : Finset (Sym2 V))
    (U : Finset V) [DecidablePred (IsInner U)] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (hT : ∀ r ∈ T, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (H P : ℕ) (z t : ℝ)
    (hJ : ∀ i, H ≤ (pool (category p) (E.filter (IsInner U)) i).card)
    (hc : ∀ i, |((T.filter fun r => category p s(r.2.1, r.2.2) = i).card : ℝ) - z| ≤ t)
    (hbudget : (P : ℝ) + z + t ≤ H) :
    ∀ i, P ≤ (pool (category p) ((E.filter (IsInner U)) \ resEdges T) i).card := by
  intro i
  apply capacity_after_overlap (category p) _ _ i H P (z + t) (hJ i)
  · rw [inter_comm, intersection_inner E U T hT, inner_category_card p T hd]
    have hi := (abs_le.mp (hc i)).2
    linarith
  · linarith

/-- Count one physical colour pair in a category. Each forbidden edge costs
at most one neighbour, even when the forbidden set contains other colours. -/
theorem category_capacity_from_parts (p : V → Fin 4) (U : Finset V)
    (J F : Finset (Sym2 V)) (i j : Fin 4) (c : Fin 3) (s b f : ℕ)
    (hij : i ≠ j) (hcat : categoryTab i j = c)
    (hi : s ≤ (U.filter fun v => p v = i).card)
    (hj : b + f ≤ (U.filter fun v => p v = j).card)
    (hF : ∀ v, incidentLoad F v ≤ f)
    (hJ : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ J) :
    s * b ≤ (pool (category p) J c).card := by
  classical
  let A := U.filter fun v => p v = i
  let B := U.filter fun v => p v = j
  let N := fun u => B.filter fun v => s(u, v) ∉ F
  have hN : ∀ u ∈ A, b ≤ (N u).card := by
    intro u _
    have hbad : (B.filter fun v => s(u, v) ∈ F).card ≤ f :=
      (card_spoke_filter_le B F u).trans (hF u)
    have he := card_filter_add_card_filter_not (s := B) (fun v => s(u, v) ∈ F)
    change b + f ≤ B.card at hj
    change b ≤ (B.filter fun v => s(u, v) ∉ F).card
    omega
  have hout : ∀ u ∈ A, ∀ v ∈ N u, v ∉ A := by
    intro u _ v hv ha
    have hvj := (mem_filter.mp (mem_filter.mp hv).1).2
    have hvi := (mem_filter.mp ha).2
    exact hij (hvi.symm.trans hvj)
  have hedge : ∀ u ∈ A, ∀ v ∈ N u, s(u, v) ∈ pool (category p) J c := by
    intro u hu v hv
    obtain ⟨huU, hui⟩ := mem_filter.mp hu
    obtain ⟨hvB, hvF⟩ := mem_filter.mp hv
    obtain ⟨hvU, hvj⟩ := mem_filter.mp hvB
    have hne : p u ≠ p v := fun he => hij (hui.symm.trans (he.trans hvj))
    refine mem_filter.mpr ⟨hJ u huU v hvU hne hvF, ?_⟩
    change categoryTab (p u) (p v) = c
    rw [hui, hvj, hcat]
  exact (Nat.mul_le_mul_right b hi).trans
    (NeighbourPoolCapacityStage114.pool_card_lower _ A N b hN hout hedge)

/-- The three pairs 01, 02, 03 witness all three opposite-pair categories.
This lower bound deliberately uses only one pair per category. -/
theorem all_category_capacity (p : V → Fin 4) (U : Finset V)
    (J F : Finset (Sym2 V)) (s b f : ℕ)
    (hsize : ∀ i, s ≤ (U.filter fun v => p v = i).card)
    (hroom : ∀ i, b + f ≤ (U.filter fun v => p v = i).card)
    (hF : ∀ v, incidentLoad F v ≤ f)
    (hJ : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ J) :
    ∀ c, s * b ≤ (pool (category p) J c).card := by
  intro c
  have hp : ∀ c : Fin 3, ∃ j : Fin 4, (0 : Fin 4) ≠ j ∧ categoryTab 0 j = c := by
    decide
  obtain ⟨j, hj, hc⟩ := hp c
  exact category_capacity_from_parts p U J F 0 j c s b f hj hc
    (hsize 0) (hroom j) hF hJ

end PartitionedTriangleAbsorption.ChildCapacityStage127
