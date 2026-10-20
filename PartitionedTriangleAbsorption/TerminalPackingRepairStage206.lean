/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1FractionalConfinementStage205
public import PartitionedTriangleAbsorption.FiniteAbsorberStage49

/-! # Exact terminal packing repair and a false shortcut

Replacing a subpacking by a decomposition of its edges together with the
actual residue closes the original graph. Existence of that replacement is
not asserted. Integral divisibility of a subset of a decomposable reserve
is insufficient, even for F1; an existing six-cycle gives a finite witness.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TerminalPackingRepairStage206

open Finset TypedApplicationLinks

theorem whole_triangle_complement {V : Type} [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D B : Finset (Finset V))
    (hD : IsDecomp p F Q D) (hBD : B ⊆ D) :
    IsDecomp p F (Q \ B.biUnion triEdges) (D \ B) := by
  classical
  refine ⟨fun s hs => hD.1 s (mem_sdiff.mp hs).1,
    hD.2.1.subset sdiff_subset, ?_⟩
  apply Subset.antisymm
  · intro e he
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    refine mem_sdiff.mpr ⟨hD.2.2 ▸ mem_biUnion.mpr ⟨s, (mem_sdiff.mp hs).1, hes⟩, ?_⟩
    intro heB
    obtain ⟨b, hb, heb⟩ := mem_biUnion.mp heB
    have hne : s ≠ b := fun h => (mem_sdiff.mp hs).2 (h ▸ hb)
    exact disjoint_left.mp (hD.2.1 (mem_sdiff.mp hs).1 (hBD hb) hne) hes heb
  · intro e he
    obtain ⟨heQ, heB⟩ := mem_sdiff.mp he
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp (hD.2.2.symm ▸ heQ)
    exact mem_biUnion.mpr ⟨s, mem_sdiff.mpr ⟨hs,
      fun hsB => heB (mem_biUnion.mpr ⟨s, hsB, hes⟩)⟩, hes⟩

theorem close_by_subpacking_repair {V : Type} [DecidableEq V] {t : ℕ}
    (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (E Q : Finset (Sym2 V)) (D B : Finset (Finset V))
    (hD : IsDecomp p F Q D) (hBD : B ⊆ D) (hQE : Q ⊆ E)
    (hrepair : HasDecomp p F (B.biUnion triEdges ∪ (E \ Q))) :
    HasDecomp p F E := by
  classical
  let A := B.biUnion triEdges
  have hAQ : A ⊆ Q := by
    rw [← hD.2.2]
    exact biUnion_subset_biUnion_of_subset_left triEdges hBD
  have hrest : HasDecomp p F (Q \ A) :=
    ⟨D \ B, whole_triangle_complement p F Q D B hD hBD⟩
  have hdis : Disjoint (Q \ A) (A ∪ (E \ Q)) := by
    apply disjoint_left.mpr
    intro e he hother
    rcases mem_union.mp hother with ha | hj
    · exact (mem_sdiff.mp he).2 ha
    · exact (mem_sdiff.mp hj).2 (mem_sdiff.mp he).1
  have hcover : (Q \ A) ∪ (A ∪ (E \ Q)) = E := by
    rw [← union_assoc, sdiff_union_of_subset hAQ, union_sdiff_of_subset hQE]
  rw [← hcover]
  exact hrest.union hrepair hdis

def part4 (v : Fin 7) : Fin 4 := if FiniteAbsorberStage49.part v = 0 then 0 else 2

set_option maxRecDepth 4096 in
theorem F1_divisibility_is_not_terminal_absorption :
    ∃ X J : Finset (Sym2 (Fin 7)), J ⊆ X ∧ HasDecomp part4 F1 X ∧
      IsIntDiv part4 F1 J ∧ ¬ HasDecomp part4 F1 J := by
  have ht (j : Fin 4) : ∀ s ∈ FiniteAbsorberStage49.decomposition j,
      IsTypedTri part4 F1 s := by
    fin_cases j <;>
      unfold FiniteAbsorberStage49.decomposition IsTypedTri part4
        FiniteAbsorberStage49.part F1 <;> decide
  have hd (j : Fin 4) : HasDecomp part4 F1
      (FiniteAbsorberStage49.auxiliary ∪ FiniteAbsorberStage49.residue j) :=
    ⟨FiniteAbsorberStage49.decomposition j, ht j,
      FiniteAbsorberStage49.decomposition_disjoint j,
      FiniteAbsorberStage49.decomposition_edges j⟩
  have hA : HasDecomp part4 F1 FiniteAbsorberStage49.auxiliary := by
    simpa only [FiniteAbsorberStage49.residue, Matrix.cons_val_zero, union_empty] using hd 0
  let X := FiniteAbsorberStage49.auxiliary ∪ FiniteAbsorberStage49.residue 1
  let J := FiniteAbsorberStage49.residue 1
  have heq : X \ FiniteAbsorberStage49.auxiliary = J := by
    apply Subset.antisymm
    · intro e he
      rcases mem_union.mp (mem_sdiff.mp he).1 with heA | heJ
      · exact False.elim ((mem_sdiff.mp he).2 heA)
      · exact heJ
    · intro e heJ
      exact mem_sdiff.mpr ⟨mem_union_right _ heJ, fun heA =>
        disjoint_left.mp (FiniteAbsorberStage49.disjoint_residue 1) heA heJ⟩
  have hi : IsIntDiv part4 F1 J := by
    rw [← heq]
    exact isIntDiv_sdiff_of_hasDecomp (isIntDiv_of_hasDecomp (hd 1)) hA subset_union_left
  refine ⟨X, J, subset_union_right, hd 1, hi, ?_⟩
  rintro ⟨D, htyped, _, hunion⟩
  have hD : D = ∅ := eq_empty_iff_forall_notMem.mpr (by
    intro s hs
    apply FiniteAbsorberStage49.cycle_no_triangle s (htyped s hs).1
    intro e he
    change e ∈ J
    rw [← hunion]
    exact mem_biUnion.mpr ⟨s, hs, he⟩)
  have hempty : J = ∅ := by rw [← hunion, hD]; simp
  have hedge : s(0, 1) ∈ J := by decide
  simp [hempty] at hedge


end PartitionedTriangleAbsorption.TerminalPackingRepairStage206
