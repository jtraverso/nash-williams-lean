/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniformBoundedCoreStage104

/-! # The remaining packing obligation for terminal-core absorption

This consumer derives divisibility of the actual leftover. It records the
precise missing output of cover-down: confinement to X while avoiding C.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BoundedCoreStage104

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ}
  {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Close the exact original edge set, not a separately chosen residual. -/
theorem hasDecomp_of_confined_packing (E C X Q : Finset (Sym2 V))
    (hE : IsIntDiv p F E) (hCE : C ⊆ E) (hC : HasDecomp p F C)
    (hall : ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (C ∪ L))
    (hQ : HasDecomp p F Q) (hQE : Q ⊆ E \ C)
    (htail : E \ (C ∪ Q) ⊆ X) : HasDecomp p F E := by
  have hQsub : Q ⊆ E := hQE.trans sdiff_subset
  have hQC : Disjoint Q C := by
    rw [disjoint_left]
    exact fun e he hc => (mem_sdiff.mp (hQE he)).2 hc
  have hCQ : C ∪ Q ⊆ E := union_subset hCE hQsub
  have hdec : HasDecomp p F (C ∪ Q) := hC.union hQ hQC.symm
  have hdiv := isIntDiv_sdiff_of_hasDecomp hE hdec hCQ
  have htaildec := hall _ htail hdiv
  have hQL : Disjoint Q (E \ (C ∪ Q)) := by
    rw [disjoint_left]
    exact fun e he hl => (mem_sdiff.mp hl).2 (mem_union_right _ he)
  have hwhole := hQ.union htaildec (disjoint_union_right.mpr ⟨hQC, hQL⟩)
  have hcover : Q ∪ (C ∪ (E \ (C ∪ Q))) = E := by
    rw [← union_assoc, union_comm Q C]
    exact union_sdiff_of_subset hCQ
  rw [hcover] at hwhole
  exact hwhole

end PartitionedTriangleAbsorption.BoundedCoreStage104
