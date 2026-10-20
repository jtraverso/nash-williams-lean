/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SelectedCoverDownBasicStage122

/-! # Extracting genuinely independent bounded-read queries

The conflict count includes the query itself. No independence is inferred
from edge-disjoint output objects: the full sets of random coordinates must
be disjoint.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.DisjointQueriesStage123

open Finset

variable {I E : Type*} [DecidableEq E]

theorem conflict_card_le (s : Finset I) (B : I → Finset E) (a : I) (r d : ℕ)
    (hsize : (B a).card ≤ r)
    (hread : ∀ e ∈ B a, (s.filter fun i => e ∈ B i).card ≤ d) :
    (s.filter fun i => ¬ Disjoint (B a) (B i)).card ≤ r * d := by
  classical
  have hsub : (s.filter fun i => ¬ Disjoint (B a) (B i)) ⊆
      (B a).biUnion (fun e => s.filter fun i => e ∈ B i) := by
    intro i hi
    obtain ⟨his, hnd⟩ := mem_filter.mp hi
    obtain ⟨e, hea, hei⟩ := not_disjoint_iff.mp hnd
    exact mem_biUnion.mpr ⟨e, hea, mem_filter.mpr ⟨his, hei⟩⟩
  calc
    _ ≤ ((B a).biUnion (fun e => s.filter fun i => e ∈ B i)).card := card_le_card hsub
    _ ≤ ∑ e ∈ B a, (s.filter fun i => e ∈ B i).card := card_biUnion_le
    _ ≤ ∑ _e ∈ B a, d := sum_le_sum hread
    _ = (B a).card * d := by simp
    _ ≤ r * d := Nat.mul_le_mul_right d hsize

/-- Greedy extraction loses only the maximum number of intersecting blocks. -/
theorem exists_disjoint (s : Finset I) (B : I → Finset E) (d : ℕ)
    (hne : ∀ i ∈ s, (B i).Nonempty)
    (hdeg : ∀ i ∈ s, (s.filter fun j => ¬ Disjoint (B i) (B j)).card ≤ d) :
    ∃ t ⊆ s, (t : Set I).PairwiseDisjoint B ∧ s.card ≤ d * t.card := by
  classical
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases hs : s = ∅
    · subst s
      exact ⟨∅, subset_rfl, by simp, by simp⟩
    obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr hs
    let c := s.filter fun j => ¬ Disjoint (B a) (B j)
    have hac : a ∈ c := mem_filter.mpr ⟨ha, by
      simpa using (hne a ha).ne_empty⟩
    have hcs : c ⊆ s := filter_subset _ _
    obtain ⟨t, hts, htd, hcard⟩ := ih (s \ c) (sdiff_ssubset hcs ⟨a, hac⟩)
      (fun i hi => hne i (mem_sdiff.mp hi).1)
      (fun i hi => (card_le_card (filter_subset_filter _ sdiff_subset)).trans
        (hdeg i (mem_sdiff.mp hi).1))
    have hat : a ∉ t := fun h => (mem_sdiff.mp (hts h)).2 hac
    refine ⟨insert a t, insert_subset ha (hts.trans sdiff_subset), ?_, ?_⟩
    · rw [coe_insert]
      apply htd.insert
      intro j hj _
      have hjc := (mem_sdiff.mp (hts hj)).2
      by_contra hn
      exact hjc (mem_filter.mpr ⟨(mem_sdiff.mp (hts hj)).1, hn⟩)
    · rw [card_insert_of_notMem hat, Nat.mul_add, Nat.mul_one]
      have heq := card_sdiff_add_card_eq_card hcs
      have hcd := hdeg a ha
      change c.card ≤ d at hcd
      omega

theorem exists_disjoint_of_read (s : Finset I) (B : I → Finset E) (r d : ℕ)
    (hne : ∀ i ∈ s, (B i).Nonempty)
    (hsize : ∀ i ∈ s, (B i).card ≤ r)
    (hread : ∀ e, (s.filter fun i => e ∈ B i).card ≤ d) :
    ∃ t ⊆ s, (t : Set I).PairwiseDisjoint B ∧ s.card ≤ (r * d) * t.card := by
  exact exists_disjoint s B (r * d) hne
    (fun i hi => conflict_card_le s B i r d (hsize i hi) (fun e _ => hread e))

end PartitionedTriangleAbsorption.DisjointQueriesStage123
