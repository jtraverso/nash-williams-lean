/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AnnularInvariantStage136

/-! # Transport an actual-host packing to the fixed-reference invariant

The physical producer measures its load inside the actual host. Since the
packing lies in that host, this equals its load inside the reference host.
This bridge reuses Stage136's transition without assuming pristine children.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingTransitionStage137

open Finset CoverDownStage105 AntiEdgeSelection TypedApplicationLinks AnnularInvariantStage136

variable {V : Type*} [DecidableEq V]

/-- Restricting a contained packing to an inner set ignores missing edges. -/
theorem packing_inter_inner_eq (E H P : Finset (Sym2 V)) (U : Finset V)
    (hHE : H ⊆ E) (hPH : P ⊆ H) : P ∩ inner H U = P ∩ inner E U := by
  ext e
  simp only [mem_inter, mem_inner]
  constructor
  · rintro ⟨hp, hh, hi⟩
    exact ⟨hp, hHE hh, hi⟩
  · rintro ⟨hp, _, hi⟩
    exact ⟨hp, hPH hp, hi⟩

/-- The same constructed packing closes the deterministic annular transition.
Existence of the packing is supplied by the physical producer, not this bridge. -/
theorem actual_host_advance (p : V → Fin 4) (E D H P : Finset (Sym2 V))
    (hH : H = E \ D) (U K : Finset V)
    (hclean : Disjoint D (inner E U)) (hP : P ⊆ H)
    (hconf : H \ P ⊆ inner H U) (hdiv : IsIntDiv p F3 H)
    (hdec : HasDecomp p F3 P) (hprotect : Disjoint P (inner E K))
    (load : ℝ) (hload : DegBounded (P ∩ inner H U) load) :
    let D' := inner E U \ (H \ P)
    D' = P ∩ inner E U ∧ Disjoint D' (inner E K) ∧ DegBounded D' load ∧
      IsIntDiv p F3 (inner E U \ D') := by
  have hHE : H ⊆ E := by rw [hH]; exact sdiff_subset
  have hinner : inner H U ⊆ inner E U := by
    intro e he
    obtain ⟨hh, hi⟩ := (mem_inner H U e).mp he
    exact (mem_inner E U e).mpr ⟨hHE hh, hi⟩
  have hload' : DegBounded (P ∩ inner E U) load := by
    rw [← packing_inter_inner_eq E H P U hHE hP]
    exact hload
  subst H
  exact annular_advance p E D P U K hclean (hconf.trans hinner)
    hdiv hdec hP hprotect load hload'

end PartitionedTriangleAbsorption.PackingTransitionStage137
