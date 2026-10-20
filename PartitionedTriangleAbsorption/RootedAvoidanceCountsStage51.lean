/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.HingeCounting

/-! # Extra support constraints genuinely remove free choices

These counts apply only to excluded vertices outside the fixed roots. An
edge whose two endpoints are roots imposes no extra support constraint.
No replacement of the returned `Hingeful` definition is introduced.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51

open Finset PhysicalHinge

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem one_extra_vertex (K : Finset (Finset (Sym2 V))) (R : Finset V)
    (i : ℕ) (v : V) (hv : v ∉ R) (hi : R.card + 1 ≤ i)
    (hroot : ∀ H ∈ K, R ⊆ support H) (horder : ∀ H ∈ K, (support H).card = i) :
    (K.filter (fun H => v ∈ support H)).card ≤
      Nat.choose (Fintype.card V - (R.card + 1)) (i - (R.card + 1)) *
        2 ^ Nat.choose (i + 1) 2 := by
  have hc : (insert v R).card = R.card + 1 := card_insert_of_notMem hv
  have hcount := rooted_edge_sets_card_le (K.filter (fun H => v ∈ support H))
    (insert v R) i (by simpa only [hc] using hi)
    (fun H hH => insert_subset_iff.mpr
      ⟨(mem_filter.mp hH).2, hroot H (mem_filter.mp hH).1⟩)
    (fun H hH => horder H (mem_filter.mp hH).1)
  simpa only [hc] using hcount

theorem two_extra_vertices (K : Finset (Finset (Sym2 V))) (R : Finset V)
    (i : ℕ) (u v : V) (hu : u ∉ R) (hv : v ∉ R) (huv : u ≠ v)
    (hi : R.card + 2 ≤ i)
    (hroot : ∀ H ∈ K, R ⊆ support H) (horder : ∀ H ∈ K, (support H).card = i) :
    (K.filter (fun H => u ∈ support H ∧ v ∈ support H)).card ≤
      Nat.choose (Fintype.card V - (R.card + 2)) (i - (R.card + 2)) *
        2 ^ Nat.choose (i + 1) 2 := by
  have hv' : v ∉ insert u R := by simp [hv,huv.symm]
  have hc : (insert v (insert u R)).card = R.card + 2 := by
    rw [card_insert_of_notMem hv', card_insert_of_notMem hu]
  have hcount := rooted_edge_sets_card_le
    (K.filter (fun H => u ∈ support H ∧ v ∈ support H))
    (insert v (insert u R)) i (by simpa only [hc] using hi)
    (fun H hH => insert_subset_iff.mpr ⟨(mem_filter.mp hH).2.2,
      insert_subset_iff.mpr ⟨(mem_filter.mp hH).2.1, hroot H (mem_filter.mp hH).1⟩⟩)
    (fun H hH => horder H (mem_filter.mp hH).1)
  simpa only [hc] using hcount

end PartitionedTriangleAbsorption.RootedAvoidanceCountsStage51
