/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CongestionRootedEmbedding

/-! # Part-preserving greedy selection with physical edge exclusions

The supply is a concrete common-neighbour count in each part, including the
empty query. It is stronger than anti-edgefulness and is an explicit input.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedEmbeddingSelection

open Finset RootedEmbeddingSelection AntiEdgeSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def typedNeighbours (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (i : Fin t) : Finset V :=
  univ.filter (fun w => p w = i ∧ ∀ u ∈ S, G.Adj u w)

def Supply (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (a : ℝ) : Prop :=
  ∀ S : Finset V, S.card ≤ D → ∀ i : Fin t, a ≤ (typedNeighbours p G S i).card

theorem exists_avoiding (p : V → Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ℕ) (a d : ℝ) (hs : Supply p G D a)
    (S Z : Finset V) (hS : S.card ≤ D) (B : Finset (Sym2 V))
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : (Z.card : ℝ) + D * d < a) (i : Fin t) :
    ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧
      ∀ u ∈ S, s(u,w) ∉ B := by
  let W := typedNeighbours p G S i
  have hsum : (∑ u ∈ S, (incidentLoad B u : ℝ)) ≤ (D : ℝ) * d := by
    calc
      _ ≤ (S.card : ℝ) * d := by
        simpa only [incidentLoad, sum_const, nsmul_eq_mul] using
          (sum_le_sum (s := S) fun u _ => hB u)
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hd
  have hcount := available_card_budget W Z S B
  have hpos : 0 < (W \ (Z ∪ blockedMany B S)).card := by
    by_contra h
    have hz : (W \ (Z ∪ blockedMany B S)).card = 0 := by omega
    rw [hz, Nat.zero_add] at hcount
    have hr : (W.card : ℝ) ≤ Z.card + ∑ u ∈ S, (incidentLoad B u : ℝ) := by
      exact_mod_cast hcount
    have hsupply := hs S hS i
    change a ≤ (W.card : ℝ) at hsupply
    linarith
  obtain ⟨w, hw⟩ := card_pos.mp hpos
  obtain ⟨hw, hbad⟩ := mem_sdiff.mp hw
  have htyped := (mem_filter.mp hw).2
  refine ⟨w, htyped.1, htyped.2, ?_, ?_⟩
  · intro hz
    exact hbad (mem_union.mpr (Or.inl hz))
  · intro u hu he
    exact hbad (mem_union.mpr (Or.inr (mem_biUnion.mpr
      ⟨u, hu, mem_filter.mpr ⟨mem_univ _, he⟩⟩)))

end PartitionedTriangleAbsorption.TypedEmbeddingSelection
