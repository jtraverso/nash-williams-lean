/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic
public import Mathlib.Data.Finset.Card
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-! Graph-to-candidate counts for the radial sampler. Damage is charged to
actual incident edges; no fractional seed or round decomposition is assumed. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset

variable {V : Type*} [DecidableEq V]

/-- Removing the grandchild and damaged radials loses at most their two
separate rootwise budgets. -/
theorem root_candidate_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (W Z : Finset V) (F : Finset (Sym2 V)) (x : V) :
    (W.filter (G.Adj x)).card ≤
      ((W \ Z).filter (fun z => G.Adj x z ∧ s(x, z) ∉ F)).card + Z.card +
        (F.filter (fun e => x ∈ e)).card := by
  classical
  let A := W.filter (G.Adj x)
  let C := (W \ Z).filter (fun z => G.Adj x z ∧ s(x, z) ∉ F)
  let damaged := W.filter (fun z => s(x, z) ∈ F)
  have hmiss : A \ C ⊆ Z ∪ damaged := by
    intro z hz
    obtain ⟨hzA, hzC⟩ := mem_sdiff.mp hz
    obtain ⟨hzW, hzAdj⟩ := mem_filter.mp hzA
    by_cases hzZ : z ∈ Z
    · exact mem_union_left _ hzZ
    · refine mem_union_right _ (mem_filter.mpr ⟨hzW, ?_⟩)
      by_contra hzF
      exact hzC (mem_filter.mpr ⟨mem_sdiff.mpr ⟨hzW, hzZ⟩, hzAdj, hzF⟩)
  have hdamaged : damaged.card ≤ (F.filter (fun e => x ∈ e)).card := by
    refine card_le_card_of_injOn (fun z => s(x, z)) ?_ ?_
    · intro z hz
      exact mem_filter.mpr ⟨(mem_filter.mp hz).2, by simp⟩
    · intro z _ z' _ heq
      exact Sym2.congr_right.mp heq
  have hcard := card_le_card_sdiff_add_card (s := A) (t := C)
  have hmissing := (card_le_card hmiss).trans (card_union_le Z damaged)
  dsimp only [A, C] at hcard hmissing
  omega

/-- For every vertex of the parent (not merely roots), candidate common
neighbours lose at most the non-neighbours in the whole child. -/
theorem candidate_common_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (W C : Finset V) (hC : C ⊆ W) (v : V) :
    C.card + (W.filter (G.Adj v)).card ≤
      W.card + (C.filter (G.Adj v)).card := by
  have hunion : C ∪ W.filter (G.Adj v) ⊆ W := union_subset hC (filter_subset _ _)
  have hinter : C ∩ W.filter (G.Adj v) = C.filter (G.Adj v) := by
    ext z
    simp only [mem_inter, mem_filter]
    constructor
    · rintro ⟨hzC, _, hzAdj⟩
      exact ⟨hzC, hzAdj⟩
    · rintro ⟨hzC, hzAdj⟩
      exact ⟨hzC, hC hzC, hzAdj⟩
  have hcard := card_union_add_card_inter C (W.filter (G.Adj v))
  rw [hinter] at hcard
  have := card_le_card hunion
  omega

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.root_candidate_count
#print axioms NashWilliams18.Case124.BoundedCore.candidate_common_count
