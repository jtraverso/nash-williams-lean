/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F3ReserveTrimStage109

/-! # Lower bounds on a physical mutable pool from neighbour witnesses

An oriented bipartite family is counted without double counting unordered
edges. Every witness is required to lie in the actual mutable pool.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.NeighbourPoolCapacityStage114

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem pool_card_lower (R : Finset (Sym2 V)) (A : Finset V) (B : V → Finset V)
    (b : ℕ) (hB : ∀ u ∈ A, b ≤ (B u).card)
    (hout : ∀ u ∈ A, ∀ v ∈ B u, v ∉ A)
    (hedge : ∀ u ∈ A, ∀ v ∈ B u, s(u, v) ∈ R) :
    A.card * b ≤ R.card := by
  classical
  let stars := fun u => (B u).image (fun v => s(u, v))
  have hcard : ∀ u, (stars u).card = (B u).card := by
    intro u
    apply card_image_of_injective
    intro v w h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hdis : (A : Set V).PairwiseDisjoint stars := by
    intro u hu u' hu' hne
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨v, hv, rfl⟩ := mem_image.mp he
    obtain ⟨v', hv', hh⟩ := mem_image.mp he'
    rcases Sym2.eq_iff.mp hh with hh | hh
    · exact hne hh.1.symm
    · exact hout u' hu' v' hv' (hh.2 ▸ hu)
  have hsub : A.biUnion stars ⊆ R := by
    intro e he
    obtain ⟨u, hu, he⟩ := mem_biUnion.mp he
    obtain ⟨v, hv, rfl⟩ := mem_image.mp he
    exact hedge u hu v hv
  calc
    A.card * b = ∑ _u ∈ A, b := by simp
    _ ≤ ∑ u ∈ A, (stars u).card := sum_le_sum (fun u hu => by rw [hcard]; exact hB u hu)
    _ = (A.biUnion stars).card := (card_biUnion hdis).symm
    _ ≤ R.card := card_le_card hsub

end PartitionedTriangleAbsorption.NeighbourPoolCapacityStage114
