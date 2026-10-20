/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveConfinementStage195

/-! # Geometry of common-neighbour trials sampled by packing triangles

Each query uses at most two packing blocks. Each block participates in at
most two witnesses of a fixed root query. Probability bounds are separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingReserveBlocksStage196

open Finset

variable {V : Type} [DecidableEq V]

theorem edge_block_unique {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (e : Sym2 V) :
    (D.filter fun s => e ∈ triEdges s).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro s hs s' hs'
  by_contra hne
  exact disjoint_left.mp (hD.2.1 (mem_filter.mp hs).1 (mem_filter.mp hs').1 hne)
    (mem_filter.mp hs).2 (mem_filter.mp hs').2

theorem query_uses_at_most_two_blocks {t : ℕ} (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (Q : Finset (Sym2 V))
    (D : Finset (Finset V)) (hD : IsDecomp p F Q D) (u v w : V) :
    ((D.filter fun s => s(u, w) ∈ triEdges s) ∪
      (D.filter fun s => s(v, w) ∈ triEdges s)).card ≤ 2 := by
  classical
  have h₁ := edge_block_unique p F Q D hD s(u, w)
  have h₂ := edge_block_unique p F Q D hD s(v, w)
  have h := card_union_le (D.filter fun s => s(u, w) ∈ triEdges s)
    (D.filter fun s => s(v, w) ∈ triEdges s)
  omega

theorem query_block_fibre_le_two (s C : Finset V) (hcard : s.card = 3)
    (u v : V) (hroot : ∀ w ∈ C, w ≠ u ∧ w ≠ v)
    (hquery : ∀ w ∈ C, s(u, w) ∈ triEdges s ∨ s(v, w) ∈ triEdges s) :
    C.card ≤ 2 := by
  classical
  by_cases hC : C.Nonempty
  · obtain ⟨w, hw⟩ := hC
    have hmember : ∀ w ∈ C, w ∈ s := by
      intro w hw
      rcases hquery w hw with he | he
      · exact (TypedNibble.mem_triEdges_iff.mp he).2.1
      · exact (TypedNibble.mem_triEdges_iff.mp he).2.1
    have huorv : u ∈ s ∨ v ∈ s := by
      rcases hquery w hw with he | he
      · exact Or.inl (TypedNibble.mem_triEdges_iff.mp he).1
      · exact Or.inr (TypedNibble.mem_triEdges_iff.mp he).1
    rcases huorv with hu | hv
    · have hsub : C ⊆ s.erase u := fun w hw =>
        mem_erase.mpr ⟨(hroot w hw).1, hmember w hw⟩
      have h := card_le_card hsub
      rw [card_erase_of_mem hu, hcard] at h
      exact h
    · have hsub : C ⊆ s.erase v := fun w hw =>
        mem_erase.mpr ⟨(hroot w hw).2, hmember w hw⟩
      have h := card_le_card hsub
      rw [card_erase_of_mem hv, hcard] at h
      exact h
  · simp [not_nonempty_iff_eq_empty.mp hC]


end PartitionedTriangleAbsorption.PackingReserveBlocksStage196
