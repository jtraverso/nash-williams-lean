/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ProtectedCoreStage125

/-! # The boundary between reserve self-exclusion and nibble protection

The finite example refutes only the implication that a packing disjoint from
a reserve must avoid its connectors. It is not a counterexample to any
asymptotic decomposition theorem. The balance identity records the charge
which must be accounted for when protecting an overlapping child and reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.LateReserveStage125

open Finset TypedApplicationLinks CoverDownStage105 ReserveQueryGeometryStage123
open ReserveAwareRecutStage120

theorem self_exclusion_not_packing_avoidance :
    ∃ (p : Fin 7 → Fin 4) (r : Fin 7 × Fin 7 × Fin 7) (y z : Fin 7)
      (P : Finset (Sym2 (Fin 7))),
      HasDecomp p F3 P ∧ Disjoint P (resTri r) ∧
      Disjoint (connectors y z r) (resTri r) ∧
      connectors y z r ⊆ P ∧ (connectors y z r).Nonempty := by
  let p : Fin 7 → Fin 4 := ![0, 1, 2, 0, 1, 2, 0]
  let r : Fin 7 × Fin 7 × Fin 7 := (0, 1, 2)
  let s : Fin 7 × Fin 7 × Fin 7 := (3, 1, 5)
  let t : Fin 7 × Fin 7 × Fin 7 := (2, 4, 6)
  let P := resTri s ∪ resTri t
  have hc : ∀ u v, s(u, v) ∈ P → p u ≠ p v := by decide
  have hs : HasDecomp p F3 (resTri s) :=
    hasDecomp_resTri p P hc subset_union_left
  have ht : HasDecomp p F3 (resTri t) :=
    hasDecomp_resTri p P hc subset_union_right
  exact ⟨p, r, 3, 4, P, hs.union ht (by decide), by decide,
    by decide, by decide, by decide⟩

variable {V : Type*} [DecidableEq V]

theorem bal_union_overlap (p : V → Fin 4) (k : Fin 2)
    (A B : Finset (Sym2 V)) :
    bal p k (A ∪ B) = bal p k A + bal p k B - bal p k (A ∩ B) := by
  have hu : A ∪ B = A ∪ (B \ A) := by
    ext e
    simp only [mem_union, mem_sdiff]
    tauto
  have hd : Disjoint A (B \ A) := by
    apply disjoint_left.mpr
    intro e he h
    exact (mem_sdiff.mp h).2 he
  have hi : B \ A = B \ (A ∩ B) := by
    ext e
    simp only [mem_sdiff, mem_inter]
    tauto
  rw [hu, bal_union p k hd, hi, bal_sdiff p k inter_subset_right]
  omega

theorem overlap_charge_of_decomp (p : V → Fin 4) (k : Fin 2)
    (J R : Finset (Sym2 V)) (hR : HasDecomp p F3 R) :
    bal p k (J ∪ R) = bal p k J - bal p k (J ∩ R) := by
  rw [bal_union_overlap, bal_zero_of_hasDecomp p k hR, add_zero]

end PartitionedTriangleAbsorption.LateReserveStage125
