/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # A finite four-mode physical F0 absorber

The same six-edge auxiliary decomposes with the empty source, two distinct
six-cycles, and the two-triangle control. Vertex 6 is fresh. This certifies a
finite template only: its embedding requires a common neighbour of FOUR roots,
which does not follow from a two-root codegree bound.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FiniteAbsorberStage49

open Finset TypedApplicationLinks

def part : Fin 7 → Fin 2 := ![0, 0, 1, 0, 1, 1, 0]

def auxiliary : Finset (Sym2 (Fin 7)) :=
  {s(1,5), s(1,6), s(2,4), s(2,6), s(4,6), s(5,6)}

def residue : Fin 4 → Finset (Sym2 (Fin 7)) :=
  ![∅, {s(0,1), s(0,5), s(1,2), s(2,3), s(3,4), s(4,5)},
    {s(0,1), s(0,5), s(1,4), s(2,3), s(2,5), s(3,4)},
    {s(0,1), s(0,2), s(1,2), s(3,4), s(3,5), s(4,5)}]

def decomposition : Fin 4 → Finset (Finset (Fin 7)) :=
  ![{{1,5,6}, {2,4,6}},
    {{0,1,5}, {1,2,6}, {2,3,4}, {4,5,6}},
    {{0,1,5}, {1,4,6}, {2,3,4}, {2,5,6}},
    {{0,1,2}, {1,5,6}, {2,4,6}, {3,4,5}}]

theorem auxiliary_card : auxiliary.card = 6 := by decide

theorem disjoint_residue (j : Fin 4) : Disjoint auxiliary (residue j) := by
  fin_cases j <;> decide

set_option maxRecDepth 4096 in
theorem decomposition_typed (j : Fin 4) :
    ∀ s ∈ decomposition j, IsTypedTri part F0 s := by
  fin_cases j <;> unfold decomposition IsTypedTri part F0 <;> decide

set_option maxRecDepth 4096 in
theorem decomposition_disjoint (j : Fin 4) :
    (decomposition j : Set (Finset (Fin 7))).PairwiseDisjoint triEdges := by
  fin_cases j <;> unfold decomposition triEdges Set.PairwiseDisjoint Set.Pairwise <;> decide

theorem decomposition_edges (j : Fin 4) :
    (decomposition j).biUnion triEdges = auxiliary ∪ residue j := by
  fin_cases j <;> unfold decomposition auxiliary residue triEdges <;> decide

theorem common_absorber (j : Fin 4) : HasDecomp part F0 (auxiliary ∪ residue j) :=
  ⟨decomposition j, decomposition_typed j, decomposition_disjoint j, decomposition_edges j⟩

theorem auxiliary_decomposable : HasDecomp part F0 auxiliary := by
  simpa only [residue, Matrix.cons_val_zero, union_empty] using common_absorber 0

/-- A physical signed certificate; the negative triangle is essential. -/
theorem cycle_signed_identity (e : Sym2 (Fin 7)) :
    (if e ∈ residue 1 then (1 : ℤ) else 0) =
      (if e ∈ triEdges ({0,1,5} : Finset (Fin 7)) then 1 else 0) +
      (if e ∈ triEdges ({1,2,3} : Finset (Fin 7)) then 1 else 0) -
      (if e ∈ triEdges ({1,3,5} : Finset (Fin 7)) then 1 else 0) +
      (if e ∈ triEdges ({3,4,5} : Finset (Fin 7)) then 1 else 0) := by
  revert e
  decide

set_option maxRecDepth 4096 in
theorem cycle_no_triangle : ∀ s : Finset (Fin 7),
    s.card = 3 → ¬ triEdges s ⊆ residue 1 := by decide

theorem cycle_not_decomposable : ¬ HasDecomp part F0 (residue 1) := by
  rintro ⟨D, htyped, _, hunion⟩
  have hD : D = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
    intro s hs
    apply cycle_no_triangle s (htyped s hs).1
    intro e he
    rw [← hunion]
    exact Finset.mem_biUnion.mpr ⟨s, hs, he⟩)
  have hempty : residue 1 = ∅ := by rw [← hunion, hD]; simp
  have hedge : s(0,1) ∈ residue 1 := by decide
  simp [hempty] at hedge

end PartitionedTriangleAbsorption.FiniteAbsorberStage49
