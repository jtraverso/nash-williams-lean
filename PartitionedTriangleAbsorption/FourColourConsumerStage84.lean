/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourColourStabilityStage84
public import PartitionedTriangleAbsorption.FourClassGraphConsumerStage80
public import PartitionedTriangleAbsorption.TypedCoarseningStage81

/-! # A four-colour degree-margin consumer on the original graph

The host and its defect are canonical and all quantitative inputs are proved.
Only the original even degrees and the two necessary opposite-pair balances
are supplied. No fractional seed or structural divisibility predicate is input.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FourColourConsumerStage84

open Finset ClassRepresentativesStage65 TypedApplicationLinks TypedCoarseningStage81
  FourColourStabilityStage84 FourClassDivisibilityStage82 AntiEdgeSelection

theorem margin_four_colour_decomposition :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 / 16 ∧ ∃ N : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W], N ≤ Fintype.card W →
        ∀ (G : SimpleGraph W) [DecidableRel G.Adj] (c : G.Coloring (Fin 4)),
          (3 / 4 - eps) * Fintype.card W ≤ (G.minDegree : ℝ) →
          (∀ v, Even (G.degree v)) →
          (edgeVec c G.edgeFinset 0 1 + edgeVec c G.edgeFinset 2 3 =
            edgeVec c G.edgeFinset 0 2 + edgeVec c G.edgeFinset 1 3) →
          (edgeVec c G.edgeFinset 0 1 + edgeVec c G.edgeFinset 2 3 =
            edgeVec c G.edgeFinset 0 3 + edgeVec c G.edgeFinset 1 2) →
          ∃ D, IsDecomp c F3 G.edgeFinset D ∧
            IsDecomp (merge ∘ c) F0 G.edgeFinset D := by
  obtain ⟨eta, delta, heta, _, hd, N, hN⟩ :=
    FourClassGraphConsumerStage80.nearly_equal_decomposition
  let eps := min (1 / 16) (min (eta / 16) (delta / 4))
  have heps : 0 < eps := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have heps1 : eps ≤ 1 / 16 := min_le_left _ _
  have hscale : 16 * eps ≤ eta := by
    have hh : eps ≤ eta / 16 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hdscale : 4 * eps ≤ delta := by
    have hh : eps ≤ delta / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨eps, heps, heps1, max N 1, ?_⟩
  intro W _ _ hW G _ c hmin heven hbal1 hbal2
  classical
  have hn : 0 < Fintype.card W := by omega
  have hdeg : ∀ v, (3 / 4 - eps) * Fintype.card W ≤ (G.degree v : ℝ) := by
    intro v
    exact hmin.trans (by exact_mod_cast G.minDegree_le_degree v)
  obtain ⟨s, hs, hnear⟩ := nearly_equal_classes G c eps eta heps.le hn hscale hdeg
  let H := host (c : W → Fin 4)
  let F := H.edgeFinset \ G.edgeFinset
  have hFd : DegBounded F (delta * Fintype.card W) := by
    intro v
    exact (defect_degree_bound G c eps heps.le hdeg v).trans
      (mul_le_mul_of_nonneg_right hdscale (Nat.cast_nonneg _))
  have hcross : StructuralF3.CrossClass c G.edgeFinset := by
    intro u v he
    exact c.valid (SimpleGraph.mem_edgeFinset.mp he)
  have hdiv : IsIntDiv c F3 G.edgeFinset :=
    (isIntDiv_iff_counts c G.edgeFinset hcross).mpr
      ⟨fun v => by rw [incident_edgeFinset]; exact heven v, hbal1, hbal2⟩
  have hdelete : H.deleteEdges (F : Set (Sym2 W)) = G := canonical_delete G c
  have hE : (H.deleteEdges (F : Set (Sym2 W))).edgeFinset = G.edgeFinset :=
    SimpleGraph.edgeFinset_inj.mpr hdelete
  have hdiv' : IsIntDiv c F3 (H.deleteEdges (F : Set (Sym2 W))).edgeFinset := by
    rw [hE]
    exact hdiv
  obtain ⟨D, hD⟩ := hN W (le_of_max_le_left hW) c H F s hs (fun _ _ => Iff.rfl)
    hnear sdiff_subset hFd hdiv'
  rw [hE] at hD
  exact ⟨D, hD, F3_decomp_as_F0 c hD⟩

end PartitionedTriangleAbsorption.FourColourConsumerStage84
