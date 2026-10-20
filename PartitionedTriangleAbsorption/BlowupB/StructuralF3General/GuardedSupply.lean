/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootedEmbeddingSelection

/-! # Common-neighbour supply restricted to permitted class pairs

The guard is essential.  In a properly coloured host, a query containing a
vertex of the target class need not have any neighbour in that class.  This
definition requests neighbours only when every requested pair is permitted.
The empty query remains included.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General

open Finset AntiEdgeSelection RootedEmbeddingSelection

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def guardedNeighbours (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (i : Fin t) : Finset V :=
  univ.filter (fun w => p w = i ∧ ∀ u ∈ S, G.Adj u w)

def GuardedSupply (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (Allowed : Fin t → Fin t → Prop)
    (D : ℕ) (a : ℝ) : Prop :=
  ∀ S : Finset V, S.card ≤ D → ∀ i : Fin t,
    (∀ u ∈ S, Allowed (p u) i) → a ≤ (guardedNeighbours p G S i).card

theorem GuardedSupply.mono {p : V → Fin t} {G : SimpleGraph V}
    [DecidableRel G.Adj] {Allowed : Fin t → Fin t → Prop}
    {D D' : ℕ} {a a' : ℝ} (hs : GuardedSupply p G Allowed D a)
    (hD : D' ≤ D) (ha : a' ≤ a) : GuardedSupply p G Allowed D' a' := by
  intro S hS i hguard
  exact ha.trans (hs S (hS.trans hD) i hguard)

theorem GuardedSupply.class_card {p : V → Fin t} {G : SimpleGraph V}
    [DecidableRel G.Adj] {Allowed : Fin t → Fin t → Prop}
    {D : ℕ} {a : ℝ} (hs : GuardedSupply p G Allowed D a) (i : Fin t) :
    a ≤ (univ.filter fun w => p w = i).card := by
  simpa [guardedNeighbours] using hs ∅ (Nat.zero_le D) i (by simp)

theorem guarded_exists_avoiding (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (Allowed : Fin t → Fin t → Prop)
    (D : ℕ) (a d : ℝ) (hs : GuardedSupply p G Allowed D a)
    (S Z : Finset V) (hS : S.card ≤ D) (B : Finset (Sym2 V))
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hb : (Z.card : ℝ) + D * d < a) (i : Fin t)
    (hguard : ∀ u ∈ S, Allowed (p u) i) :
    ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧
      ∀ u ∈ S, s(u,w) ∉ B := by
  let W := guardedNeighbours p G S i
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
    have hsupply := hs S hS i hguard
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

#print axioms GuardedSupply.mono
#print axioms GuardedSupply.class_card
#print axioms guarded_exists_avoiding

end PartitionedTriangleAbsorption.StructuralF3General
