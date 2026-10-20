/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

/-! # A bounded inverse on actual four-class physical edges

The input is a balanced demand, not a supplied triangle correction. The output
is indexed by the same copies used by the nibble and cover-down consumers.
This theorem concerns the complete host; deleted hosts remain a separate step.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourClassCopyAdapterStage74

open Finset FourClassInverseStage73 TypedLoadNecessity

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem coordinates_bound (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (d : Sym2 V → ℝ) (M : ℝ) (hd : ∀ e ∈ G.edgeFinset, |d e| ≤ M) :
    EdgeBound (demandCoordinates p d) M := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals
    intro u v
    apply hd
    apply SimpleGraph.mem_edgeFinset.mpr
    apply G.mem_edgeSet.mpr
    exact (hG _ _).mpr (by simp only [class_label]; decide)

omit [DecidableEq V] in
theorem class_nonempty (p : V → Fin 4) (gamma : ℝ) (hg : 0 < gamma)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (i : Fin 4) : Nonempty (Class p i) := by
  apply Fintype.card_pos_iff.mp
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hi : (0 : ℝ) < Fintype.card (Class p i) :=
    (mul_pos hg hnR).trans_le (hsize i)
  exact_mod_cast hi

omit [DecidableEq V] in
/-- Construct the tuple correction, retaining its physical provenance. -/
theorem physical_inverse_data (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (d : Sym2 V → ℝ) (hd : RawBalanced (demandCoordinates p d))
    (gamma M : ℝ) (hg : 0 < gamma) (hM : 0 ≤ M)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hcap : ∀ e ∈ G.edgeFinset, |d e| ≤ M) :
    ∃ w : TriangleData (Class p 0) (Class p 1) (Class p 2) (Class p 3),
      physicalBoundary w = demandCoordinates p d ∧
      TriangleBound w (18 * M / (gamma ^ 3 * Fintype.card V)) := by
  let : Nonempty (Class p 0) := class_nonempty p gamma hg hn hsize 0
  let : Nonempty (Class p 1) := class_nonempty p gamma hg hn hsize 1
  let : Nonempty (Class p 2) := class_nonempty p gamma hg hn hsize 2
  let : Nonempty (Class p 3) := class_nonempty p gamma hg hn hsize 3
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hupper (i : Fin 4) :
      (Fintype.card (Class p i) : ℝ) ≤ Fintype.card V := by
    exact_mod_cast Fintype.card_subtype_le (fun v => p v = i)
  obtain ⟨w,hw,hbound⟩ := complete_four_class_inverse (demandCoordinates p d)
    ((balanced_normalize_iff _).mpr hd) (Fintype.card V) gamma M hnR hg hM
    (hupper 0) (hupper 1) (hupper 2) (hupper 3)
    (hsize 0) (hsize 1) (hsize 2) (hsize 3) (coordinates_bound p G hG d M hcap)
  exact ⟨w,hw,hbound⟩

/-- Signed correction with exact physical loads and a uniform coefficient cap. -/
theorem physical_inverse (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : ∀ u v, G.Adj u v ↔ p u ≠ p v)
    (d : Sym2 V → ℝ) (hd : RawBalanced (demandCoordinates p d))
    (gamma M : ℝ) (hg : 0 < gamma) (hM : 0 ≤ M)
    (hn : 0 < Fintype.card V)
    (hsize : ∀ i, gamma * Fintype.card V ≤ (Fintype.card (Class p i) : ℝ))
    (hcap : ∀ e ∈ G.edgeFinset, |d e| ≤ M) :
    ∃ psi : Finset V → ℝ,
      (∀ e ∈ G.edgeFinset, edgeLoad p TypedApplicationLinks.F3 G psi e = d e) ∧
      (∀ s, |psi s| ≤ 18 * M / (gamma ^ 3 * Fintype.card V)) := by
  obtain ⟨w,hw,hbound⟩ := physical_inverse_data p G hG d hd gamma M hg hM hn hsize hcap
  refine ⟨physicalWeights p w,load_eq_of_boundary p G hG w d hw,?_⟩
  exact physicalWeights_bound p w _ (by positivity) hbound

end PartitionedTriangleAbsorption.FourClassCopyAdapterStage74
