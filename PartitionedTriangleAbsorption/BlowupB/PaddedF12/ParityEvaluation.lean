/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# A partially defined additive parity on finite edge sets

The parity of F2 uses a division by two. It is additive on the class of even,
allowed edge sets, which is enough for the refiner. This interface records that
domain instead of falsely assuming an additive parity on arbitrary edge sets.
-/

namespace PaddedF12

open Finset

variable {α : Type*} [DecidableEq α]

structure ParityEvaluation (Good : Finset α → Prop) where
  empty_good : Good ∅
  union_good : ∀ {A B : Finset α}, Disjoint A B → Good A → Good B → Good (A ∪ B)
  value : Finset α → Nat
  value_lt : ∀ A, Good A → value A < 2
  empty_value : value ∅ = 0
  union_value : ∀ {A B : Finset α}, Disjoint A B → Good A → Good B →
    value (A ∪ B) = (value A + value B) % 2

namespace ParityEvaluation

variable {Good : Finset α → Prop} (q : ParityEvaluation Good)

include q

/-- Finite disjoint unions remain in the domain of the parity. -/
theorem good_biUnion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (E : ι → Finset α)
    (hdis : (S : Set ι).PairwiseDisjoint E) (hgood : ∀ i ∈ S, Good (E i)) :
    Good (S.biUnion E) := by
  induction S using Finset.induction_on with
  | empty => simpa using q.empty_good
  | insert i S hi ih =>
    rw [biUnion_insert]
    have hrest : (S : Set ι).PairwiseDisjoint E :=
      hdis.subset (by intro j hj; exact mem_insert_of_mem hj)
    have hgoods : ∀ j ∈ S, Good (E j) := fun j hj => hgood j (mem_insert_of_mem hj)
    apply q.union_good
    · rw [disjoint_biUnion_right]
      intro j hj
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))
    · exact hgood i (mem_insert_self _ _)
    · exact ih hrest hgoods

/-- Exact parity of a finite disjoint union. -/
theorem value_biUnion {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (E : ι → Finset α)
    (hdis : (S : Set ι).PairwiseDisjoint E) (hgood : ∀ i ∈ S, Good (E i)) :
    q.value (S.biUnion E) = (∑ i ∈ S, q.value (E i)) % 2 := by
  induction S using Finset.induction_on with
  | empty => simpa using q.empty_value
  | insert i S hi ih =>
    rw [biUnion_insert, sum_insert hi]
    have hrest : (S : Set ι).PairwiseDisjoint E :=
      hdis.subset (by intro j hj; exact mem_insert_of_mem hj)
    have hgoods : ∀ j ∈ S, Good (E j) := fun j hj => hgood j (mem_insert_of_mem hj)
    have hgoodi := hgood i (mem_insert_self _ _)
    have hsep : Disjoint (E i) (S.biUnion E) := by
      rw [disjoint_biUnion_right]
      intro j hj
      exact hdis (mem_insert_self _ _) (mem_insert_of_mem hj) (fun hij => hi (hij ▸ hj))
    rw [q.union_value hsep hgoodi (q.good_biUnion S E hrest hgoods), ih hrest hgoods]
    omega

end ParityEvaluation

#print axioms ParityEvaluation.good_biUnion
#print axioms ParityEvaluation.value_biUnion

end PaddedF12
