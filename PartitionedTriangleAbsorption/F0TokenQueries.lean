/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F0PatternSupply
public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeF0

/-! # Common-neighbour supply along the actual token cycle orders

Only the four active vertices of the minus token are required to be distinct.
The plus token uses all eight. Empty and single queries use positive F0 supply;
the two-root closing queries have a permitted F0 type. No embedding is assumed
to exist: the statement consumes a given, locally faithful partial assignment.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F0TokenQueries

open Finset TypedApplicationLinks TypedRefinerF0 TypedEmbeddingSelection F0PatternSupply

def support (b : Bool) : Finset (Fin 8) := if b then univ else {0,1,2,3}

def earlier (b : Bool) (j : Fin 8) : Finset (Fin 8) :=
  univ.filter (fun i => i.val < j.val ∧ s(i,j) ∈ gadget b)

theorem earlier_card_le : ∀ b j, (earlier b j).card ≤ 2 := by decide

theorem earlier_supported : ∀ b j, earlier b j ⊆ support b := by decide

theorem earlier_cases : ∀ b j,
    earlier b j = ∅ ∨ (∃ i, earlier b j = {i}) ∨
      (∃ i l, i ≠ l ∧ earlier b j = {i,l} ∧
        ({gadgetPart b i,gadgetPart b l,gadgetPart b j} : Multiset (Fin 2)) ∈ F0) := by
  decide

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem query_supply (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (alpha : ℝ) (hanti : AntiEdgeful p F0 G alpha) (hparts : PartsPresent p)
    (b : Bool) (j : Fin 8) (f : Fin 8 → V)
    (hinj : Set.InjOn f (earlier b j : Set (Fin 8)))
    (hlabels : ∀ i ∈ earlier b j, p (f i) = gadgetPart b i) :
    alpha * Fintype.card V ≤
      (typedNeighbours p G ((earlier b j).image f) (gadgetPart b j)).card := by
  rcases earlier_cases b j with hz | hs | hp
  · rw [hz, image_empty]
    exact empty_supply p G alpha hanti hparts _
  · obtain ⟨i, hi⟩ := hs
    rw [hi, image_singleton]
    exact single_supply p G alpha hanti hparts _ _
  · obtain ⟨i, l, hne, he, ht⟩ := hp
    have hi : i ∈ earlier b j := by rw [he]; simp
    have hl : l ∈ earlier b j := by rw [he]; simp
    have hf : f i ≠ f l := fun h => hne (hinj hi hl h)
    have htype : ({p (f i),p (f l),gadgetPart b j} : Multiset (Fin 2)) ∈ F0 := by
      rw [hlabels i hi, hlabels l hl]
      exact ht
    rw [he, image_insert, image_singleton]
    exact pair_supply p G alpha hanti _ _ hf _ htype

theorem query_supply_of_positive (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (alpha : ℝ) (ha : 0 < alpha) (hn : 3 ≤ Fintype.card V)
    (hanti : AntiEdgeful p F0 G alpha) (b : Bool) (j : Fin 8) (f : Fin 8 → V)
    (hinj : Set.InjOn f (earlier b j : Set (Fin 8)))
    (hlabels : ∀ i ∈ earlier b j, p (f i) = gadgetPart b i) :
    alpha * Fintype.card V ≤
      (typedNeighbours p G ((earlier b j).image f) (gadgetPart b j)).card :=
  query_supply p G alpha hanti (parts_present p G alpha ha hn hanti) b j f hinj hlabels

end PartitionedTriangleAbsorption.F0TokenQueries
