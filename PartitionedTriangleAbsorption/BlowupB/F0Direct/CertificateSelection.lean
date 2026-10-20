/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostWalkQueries

@[expose] public section

/-! # Simultaneous crossing neighbours for finitely many certificate roots -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply TypedApplicationLinks HostWalkQueries

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj] {α ε : ℝ}

def badRoots (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (R : Finset V) : Finset V :=
  R.biUnion (fun r => partSet p i \ partNbrs p G i r)

def commonRoots (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (i : Fin 2) (R : Finset V) : Finset V := partSet p i \ badRoots p G i R

theorem mem_commonRoots (i : Fin 2) (R : Finset V) (w : V) :
    w ∈ commonRoots p G i R ↔ p w = i ∧ ∀ r ∈ R, G.Adj r w := by
  constructor
  · intro hw
    obtain ⟨hp, hn⟩ := mem_sdiff.mp hw
    refine ⟨mem_partSet.mp hp, ?_⟩
    intro r hr
    by_contra hnr
    exact hn (mem_biUnion.mpr ⟨r, hr, mem_sdiff.mpr ⟨hp,
      fun h => hnr (mem_partNbrs.mp h).2⟩⟩)
  · rintro ⟨hp, hR⟩
    refine mem_sdiff.mpr ⟨mem_partSet.mpr hp, ?_⟩
    intro hn
    obtain ⟨r, hr, hw⟩ := mem_biUnion.mp hn
    exact (mem_sdiff.mp hw).2 (mem_partNbrs.mpr ⟨hp, hR r hr⟩)

theorem badRoots_card (h : HostHyp p G α ε) (i : Fin 2) (R : Finset V)
    (hRpart : ∀ r ∈ R, p r ≠ i) (hR : (R.card : ℝ) * ε ≤ 1 / 100) :
    ((badRoots p G i R).card : ℝ) ≤ 3 * Fintype.card V / 200 := by
  have hc := card_biUnion_le (s := R) (t := fun r => partSet p i \ partNbrs p G i r)
  have hcr := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcr
  have hsum : (∑ r ∈ R, ((partSet p i \ partNbrs p G i r).card : ℝ)) ≤
      (R.card : ℝ) * (3 * ε * Fintype.card V / 2) := by
    have hs := sum_le_sum (fun r hr => cross_missing_bound h i r (hRpart r hr))
    simpa only [sum_const, nsmul_eq_mul] using hs
  have hm := mul_le_mul_of_nonneg_right hR
    (Nat.cast_nonneg (Fintype.card V) : (0 : ℝ) ≤ Fintype.card V)
  change ((badRoots p G i R).card : ℝ) ≤ _ at hcr
  nlinarith only [hcr, hsum, hm]

theorem exists_commonRoots (h : HostHyp p G α ε) (hε : ε ≤ 1 / 100)
    (hn : 0 < Fintype.card V) (i : Fin 2) (R : Finset V)
    (hRpart : ∀ r ∈ R, p r ≠ i) (hR : (R.card : ℝ) * ε ≤ 1 / 100) :
    ∃ w, p w = i ∧ ∀ r ∈ R, G.Adj r w := by
  have hb := badRoots_card h i R hRpart hR
  have hc := card_le_card_sdiff_add_card (s := partSet p i) (t := badRoots p G i R)
  have hcr := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcr
  change ((partSet p i).card : ℝ) ≤ (commonRoots p G i R).card +
    (badRoots p G i R).card at hcr
  have hs := h.part_size i
  have hnr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have he := mul_le_mul_of_nonneg_right hε hnr.le
  have hp : (0 : ℝ) < (commonRoots p G i R).card := by
    nlinarith only [hb, hcr, hs, he, hnr]
  have hpN : 0 < (commonRoots p G i R).card := by exact_mod_cast hp
  obtain ⟨w, hw⟩ := card_pos.mp hpN
  exact ⟨w, (mem_commonRoots i R w).mp hw⟩

theorem exists_internal_edge_commonRoots (h : HostHyp p G α ε)
    (hε : ε ≤ 1 / 100) (hn : 0 < Fintype.card V) (i : Fin 2) (R : Finset V)
    (hRpart : ∀ r ∈ R, p r ≠ i) (hR : (R.card : ℝ) * ε ≤ 1 / 100) :
    ∃ b b', p b = i ∧ p b' = i ∧ G.Adj b b' ∧
      (∀ r ∈ R, G.Adj r b) ∧ (∀ r ∈ R, G.Adj r b') := by
  obtain ⟨b, hbi, hbR⟩ := exists_commonRoots h hε hn i R hRpart hR
  have hb := badRoots_card h i R hRpart hR
  have hc := card_le_card_sdiff_add_card (s := partNbrs p G i b)
    (t := badRoots p G i R)
  have hcr := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcr
  have hd := h.degree_to_lower b i
  change (1 / 4 - ε) * Fintype.card V ≤ ((partNbrs p G i b).card : ℝ) at hd
  have hnr : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have he := mul_le_mul_of_nonneg_right hε hnr.le
  have hp : (0 : ℝ) < (partNbrs p G i b \ badRoots p G i R).card := by
    nlinarith only [hb, hcr, hd, he, hnr]
  have hpN : 0 < (partNbrs p G i b \ badRoots p G i R).card := by exact_mod_cast hp
  obtain ⟨b', hb'⟩ := card_pos.mp hpN
  obtain ⟨hb'N, hb'bad⟩ := mem_sdiff.mp hb'
  obtain ⟨hb'i, hbb'⟩ := mem_partNbrs.mp hb'N
  refine ⟨b, b', hbi, hb'i, hbb', hbR, ?_⟩
  exact ((mem_commonRoots i R b').mp
    (mem_sdiff.mpr ⟨mem_partSet.mpr hb'i, hb'bad⟩)).2

#print axioms exists_commonRoots
#print axioms exists_internal_edge_commonRoots

end PartitionedTriangleAbsorption.BlowupB.F0Direct
