/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.GeometryBounds
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.SimplePathCounts

@[expose] public section

/-! # Short-path and fresh-neighbour queries in the original host

The hypotheses in this module are the original `HostHyp` bounds.  Every
auxiliary common-neighbour set is defined from the actual graph.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HostWalkQueries

open Finset CloneSupply TypedApplicationLinks WalkSupply SimplePathCounts

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε : ℝ}

theorem partNbrs_eq_neighbors (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (u : V) : partNbrs p G i u = neighbors G (partSet p i) u := by
  ext v
  simp only [mem_partNbrs, mem_neighbors, mem_partSet]

theorem partNbrs_subset (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (u : V) : partNbrs p G i u ⊆ partSet p i := by
  rw [partNbrs_eq_neighbors]
  exact neighbors_subset G _ u

theorem commonPart_subset (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (a b : V) : commonPart p G i a b ⊆ partSet p i := by
  intro u hu
  exact mem_partSet.mpr (mem_commonPart.mp hu).1

theorem order_le_four_part (h : HostHyp p G α ε) (hε : ε ≤ 1 / 2) (i : Fin 2) :
    (Fintype.card V : ℝ) ≤ 4 * (partSet p i).card := by
  have hs := h.part_size i
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith

theorem halfRegular_of_host (h : HostHyp p G α ε) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (θ : ℝ) (hθ : 5 * ε ≤ θ) (i : Fin 2) : HalfRegular G (partSet p i) θ := by
  have hn := order_le_four_part h hε i
  have hslo := h.part_size i
  have hshi := h.part_upper i
  have he := mul_le_mul_of_nonneg_left hn (show (0 : ℝ) ≤ 5 * ε / 4 by positivity)
  have ht := mul_le_mul_of_nonneg_right hθ
    (Nat.cast_nonneg (partSet p i).card : (0 : ℝ) ≤ (partSet p i).card)
  intro u hu
  have hpu := mem_partSet.mp hu
  have hlo := h.internal_lower u
  have hhi := h.internal_upper u
  rw [hpu, partDeg, partNbrs_eq_neighbors] at hlo hhi
  constructor <;> nlinarith only [hslo, hshi, hlo, hhi, he, ht]

theorem cross_missing_bound (h : HostHyp p G α ε) (i : Fin 2) (u : V) (hu : p u ≠ i) :
    ((partSet p i \ partNbrs p G i u).card : ℝ) ≤ 3 * ε * Fintype.card V / 2 := by
  have hc := card_sdiff_add_card_eq_card (partNbrs_subset p G i u)
  have hcr := congrArg (fun k : ℕ => (k : ℝ)) hc
  push_cast at hcr
  have hp := h.part_upper i
  have hd := h.cross_to_lower u i hu
  change (1 / 2 - ε) * Fintype.card V ≤ ((partNbrs p G i u).card : ℝ) at hd
  linarith

theorem common_missing_bound (h : HostHyp p G α ε) (i : Fin 2) (a b : V)
    (ha : p a ≠ i) (hb : p b ≠ i) :
    ((partSet p i \ commonPart p G i a b).card : ℝ) ≤ 3 * ε * Fintype.card V := by
  have hc := card_sdiff_add_card_eq_card (commonPart_subset p G i a b)
  have hcr := congrArg (fun k : ℕ => (k : ℝ)) hc
  push_cast at hcr
  have hbudget : (partDeg p G i a : ℝ) + partDeg p G i b ≤
      (partSet p i).card + (commonPart p G i a b).card := by
    exact_mod_cast commonPart_card_budget p G i a b
  have hda := h.cross_to_lower a i ha
  have hdb := h.cross_to_lower b i hb
  have hp := h.part_upper i
  linarith

theorem neighbors_restrict_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (D S : Finset V) (hS : S ⊆ D) (u : V) :
    (neighbors G D u).card ≤ (neighbors G S u).card + (D \ S).card := by
  have hc := card_le_card_sdiff_add_card (s := neighbors G D u) (t := neighbors G S u)
  have hd := card_le_card (neighbors_sdiff_subset G D S u)
  omega

theorem common_degree_lower (h : HostHyp p G α ε) (hε : ε ≤ 1 / 100)
    (i : Fin 2) (a b : V) (ha : p a ≠ i) (hb : p b ≠ i)
    {u : V} (hu : u ∈ partSet p i) :
    ((partSet p i).card : ℝ) / 3 ≤ (neighbors G (commonPart p G i a b) u).card := by
  have hmiss := common_missing_bound h i a b ha hb
  have hre := neighbors_restrict_budget G (partSet p i) (commonPart p G i a b)
    (commonPart_subset p G i a b) u
  have hr := (Nat.cast_le (α := ℝ)).mpr hre
  push_cast at hr
  have hd := h.internal_lower u
  rw [mem_partSet.mp hu, partDeg, partNbrs_eq_neighbors] at hd
  have hp := h.part_upper i
  have he := mul_le_mul_of_nonneg_right hε
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)
  nlinarith only [hmiss, hr, hd, hp, he]

theorem common_walk_supply (h : HostHyp p G α ε) (hε0 : 0 ≤ ε)
    (hε : ε ≤ 1 / 100) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100)
    (hεθ : 100 * ε ≤ θ) (hscale : 100 * θ ≤ α)
    (hn : 4096 ≤ θ * Fintype.card V) (i : Fin 2)
    (hext : Nonextreme G (partSet p i) α) (a b : V)
    (ha : p a ≠ i) (hb : p b ≠ i) :
    1024 ≤ θ * (partSet p i).card ∧
    ∀ u ∈ commonPart p G i a b, ∀ v ∈ commonPart p G i a b,
      θ * ((partSet p i).card : ℝ)^2 / 2 <
        arcs G (neighbors G (commonPart p G i a b) u)
          (neighbors G (commonPart p G i a b) v) := by
  have hnm := order_le_four_part h (by linarith) i
  have hnmθ := mul_le_mul_of_nonneg_left hnm hθ0.le
  have hm : 1024 ≤ θ * (partSet p i).card := by nlinarith only [hn, hnmθ]
  have hreg := halfRegular_of_host h hε0 (by linarith) θ (by linarith) i
  have hmiss := common_missing_bound h i a b ha hb
  have hnmε := mul_le_mul_of_nonneg_left hnm (show (0 : ℝ) ≤ 3 * ε by positivity)
  have heθ := mul_le_mul_of_nonneg_right hεθ
    (Nat.cast_nonneg (partSet p i).card : (0 : ℝ) ≤ (partSet p i).card)
  have hsmall : ((partSet p i \ commonPart p G i a b).card : ℝ) ≤
      θ * (partSet p i).card / 4 := by
    nlinarith only [hmiss, hnmε, heθ, mul_nonneg hε0
      (Nat.cast_nonneg (partSet p i).card : (0 : ℝ) ≤ (partSet p i).card)]
  refine ⟨hm, ?_⟩
  intro u hu v hv
  exact arcs_neighbors_avoiding_gt G (partSet p i) (commonPart p G i a b)
    (commonPart_subset p G i a b) α θ hθ0 hθ1 hscale (by linarith) hreg hext hsmall hu hv

/-- One unrestricted degree query and up to three crossing conditions, with
at most six explicitly forbidden vertices. -/
def freshInternal (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (u : V) (R Q : Finset V) : Finset V :=
  partNbrs p G i u \ (Q ∪ R.biUnion (fun r => partSet p i \ partNbrs p G i r))

theorem freshInternal_mem (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (u : V) (R Q : Finset V) (w : V) :
    w ∈ freshInternal p G i u R Q ↔
      p w = i ∧ G.Adj u w ∧ w ∉ Q ∧ ∀ r ∈ R, G.Adj r w := by
  constructor
  · intro hw
    obtain ⟨hwN, hwBad⟩ := mem_sdiff.mp hw
    obtain ⟨hp, hu⟩ := mem_partNbrs.mp hwN
    refine ⟨hp, hu, fun h => hwBad (mem_union_left _ h), ?_⟩
    intro r hr
    by_contra hn
    apply hwBad
    apply mem_union_right
    exact mem_biUnion.mpr ⟨r, hr, mem_sdiff.mpr ⟨mem_partSet.mpr hp,
      fun h => hn (mem_partNbrs.mp h).2⟩⟩
  · rintro ⟨hp, hu, hQ, hR⟩
    apply mem_sdiff.mpr
    refine ⟨mem_partNbrs.mpr ⟨hp, hu⟩, ?_⟩
    intro hw
    rcases mem_union.mp hw with hq | hr
    · exact hQ hq
    · obtain ⟨r, hrR, hwr⟩ := mem_biUnion.mp hr
      exact (mem_sdiff.mp hwr).2 (mem_partNbrs.mpr ⟨hp, hR r hrR⟩)

theorem freshInternal_lower (h : HostHyp p G α ε) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 96)
    (hn : (96 : ℝ) ≤ Fintype.card V) (i : Fin 2) (u : V) (R Q : Finset V)
    (hR : R.card ≤ 3) (hRpart : ∀ r ∈ R, p r ≠ i) (hQ : Q.card ≤ 6) :
    (Fintype.card V : ℝ) / 8 ≤ (freshInternal p G i u R Q).card := by
  have hnonneg : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hsum : (∑ r ∈ R, ((partSet p i \ partNbrs p G i r).card : ℝ)) ≤
      (R.card : ℝ) * (3 * ε * Fintype.card V / 2) := by
    have hs := sum_le_sum (fun r hr => cross_missing_bound h i r (hRpart r hr))
    simpa only [sum_const, nsmul_eq_mul] using hs
  have hRr : (R.card : ℝ) ≤ 3 := by exact_mod_cast hR
  have hRmul := mul_le_mul_of_nonneg_right hRr
    (show 0 ≤ 3 * ε * Fintype.card V / 2 by positivity)
  have hbad : ((R.biUnion (fun r => partSet p i \ partNbrs p G i r)).card : ℝ) ≤
      9 * ε * Fintype.card V / 2 := by
    have hb := card_biUnion_le (s := R) (t := fun r => partSet p i \ partNbrs p G i r)
    have hbr := (Nat.cast_le (α := ℝ)).mpr hb
    push_cast at hbr
    nlinarith only [hbr, hsum, hRmul]
  have hcard := card_le_card_sdiff_add_card (s := partNbrs p G i u)
    (t := Q ∪ R.biUnion (fun r => partSet p i \ partNbrs p G i r))
  have hc := (Nat.cast_le (α := ℝ)).mpr hcard
  push_cast at hc
  change ((partNbrs p G i u).card : ℝ) ≤ (freshInternal p G i u R Q).card +
    (Q ∪ R.biUnion (fun r => partSet p i \ partNbrs p G i r)).card at hc
  have huc := card_union_le Q (R.biUnion (fun r => partSet p i \ partNbrs p G i r))
  have hur := (Nat.cast_le (α := ℝ)).mpr huc
  push_cast at hur
  have hQr : (Q.card : ℝ) ≤ 6 := by exact_mod_cast hQ
  have hd := h.degree_to_lower u i
  change (1 / 4 - ε) * Fintype.card V ≤ ((partNbrs p G i u).card : ℝ) at hd
  have he := mul_le_mul_of_nonneg_right hε hnonneg
  have he0 := mul_nonneg hε0 hnonneg
  nlinarith only [hbad, hc, hur, hQr, hd, he, he0, hn]

#print axioms halfRegular_of_host
#print axioms common_walk_supply
#print axioms freshInternal_lower

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HostWalkQueries
