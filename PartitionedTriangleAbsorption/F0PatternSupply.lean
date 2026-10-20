/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0RequestLabels

/-! # Supplies for actual F0 queries of order at most two

Positive anti-edgefulness on at least three vertices forces both parts to
occur. Empty and one-root queries then have the same linear supply. Two-root
queries need an explicitly permitted F0 type; no all-pattern supply is claimed.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0PatternSupply

open Finset TypedApplicationLinks TypedEmbeddingSelection

variable {V : Type*} [Fintype V] [DecidableEq V]

def PartsPresent (p : V → Fin 2) : Prop := ∀ i, ∃ v, p v = i

theorem mixed_permitted : ∀ i k : Fin 2,
    ({i,other0 i,k} : Multiset (Fin 2)) ∈ F0 := by decide

theorem other_ne : ∀ i : Fin 2, other0 i ≠ i := by decide

theorem two_part_cases : ∀ i j : Fin 2, i = j ∨ i = other0 j := by decide

theorem pair_supply (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (alpha : ℝ) (hanti : AntiEdgeful p F0 G alpha) (u v : V) (huv : u ≠ v)
    (k : Fin 2) (ht : ({p u,p v,k} : Multiset (Fin 2)) ∈ F0) :
    alpha * Fintype.card V ≤ (typedNeighbours p G {u,v} k).card := by
  have hc := hanti _ ht (p u) (p v) k rfl u v huv rfl rfl
  have heq : univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k) =
      typedNeighbours p G {u,v} k := by
    ext w
    simp only [typedNeighbours, mem_filter, mem_univ, true_and,
      mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hu, hv, hp⟩
      exact ⟨hp, hu, G.adj_symm hv⟩
    · rintro ⟨hp, hu, hv⟩
      exact ⟨hu, G.adj_symm hv, hp⟩
  rw [heq] at hc
  exact hc

theorem query_antitone (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S T : Finset V) (hST : S ⊆ T) (k : Fin 2) :
    typedNeighbours p G T k ⊆ typedNeighbours p G S k := by
  intro w hw
  obtain ⟨_, hp, hn⟩ := mem_filter.mp hw
  exact mem_filter.mpr ⟨mem_univ _, hp, fun u hu => hn u (hST hu)⟩

theorem single_supply (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (alpha : ℝ) (hanti : AntiEdgeful p F0 G alpha) (hparts : PartsPresent p)
    (u : V) (k : Fin 2) :
    alpha * Fintype.card V ≤ (typedNeighbours p G {u} k).card := by
  obtain ⟨v, hv⟩ := hparts (other0 (p u))
  have huv : u ≠ v := by
    intro h
    subst v
    exact other_ne (p u) hv.symm
  have ht : ({p u,p v,k} : Multiset (Fin 2)) ∈ F0 := by
    rw [hv]
    exact mixed_permitted _ _
  refine (pair_supply p G alpha hanti u v huv k ht).trans ?_
  exact_mod_cast card_le_card (query_antitone p G {u} {u,v} (by simp) k)

theorem empty_supply (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (alpha : ℝ) (hanti : AntiEdgeful p F0 G alpha) (hparts : PartsPresent p)
    (k : Fin 2) :
    alpha * Fintype.card V ≤ (typedNeighbours p G ∅ k).card := by
  obtain ⟨u, _⟩ := hparts 0
  refine (single_supply p G alpha hanti hparts u k).trans ?_
  exact_mod_cast card_le_card (query_antitone p G ∅ {u} (empty_subset _) k)

omit [DecidableEq V] in
theorem parts_present (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (alpha : ℝ) (ha : 0 < alpha) (hn : 3 ≤ Fintype.card V)
    (hanti : AntiEdgeful p F0 G alpha) : PartsPresent p := by
  classical
  have hni : ¬ Function.Injective p := by
    intro hi
    have hc := Fintype.card_le_of_injective p hi
    simp only [Fintype.card_fin] at hc
    omega
  have hpair : ∃ u v : V, p u = p v ∧ u ≠ v := by
    by_contra h
    push Not at h
    exact hni (fun u v hp => h u v hp)
  obtain ⟨u, v, hp, huv⟩ := hpair
  have hs := F0RequestLabels.request_supply p G alpha hanti u v huv
  have hpositive : 0 < (typedNeighbours p G {u,v}
      (F0RequestLabels.centrePart (p u) (p v))).card := by
    have hnreal : (0 : ℝ) < Fintype.card V := by exact_mod_cast (by omega : 0 < Fintype.card V)
    exact_mod_cast lt_of_lt_of_le (mul_pos ha hnreal) hs
  obtain ⟨w, hw⟩ := card_pos.mp hpositive
  have hwpart := (mem_filter.mp hw).2.1
  have hother : p w = other0 (p u) := by
    simpa [hp, F0RequestLabels.centrePart] using hwpart
  intro i
  rcases two_part_cases i (p u) with hi | hi
  · exact ⟨u, hi.symm⟩
  · exact ⟨w, hother.trans hi.symm⟩

end PartitionedTriangleAbsorption.F0PatternSupply
