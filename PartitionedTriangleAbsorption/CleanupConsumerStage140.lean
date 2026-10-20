/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourColourConsumerStage84
public import PartitionedTriangleAbsorption.OnePartDivisibility
public import PartitionedTriangleAbsorption.SparseDeletionDegree

/-! # Consuming a physical cleanup packing

The cleanup is an explicit intermediate input: it covers every internal edge,
has bounded physical degree, and leaves the two exact F3 balances. This module
constructs the residual colouring and decomposes the same original graph. It
does not assert that such a cleanup exists for every nearly multipartite graph.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupConsumerStage140

open Finset OnePart TypedApplicationLinks TypedCoarseningStage81

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Forgetting the four labels preserves the physical triangle decomposition. -/
theorem ordinary_of_F3 (p : V → Fin 4) {E : Finset (Sym2 V)}
    (hE : HasDecomp p F3 E) : HasDecomp part1 triFam E := by
  have hmap : ∀ τ ∈ F3, τ.map (fun _ : Fin 4 => (0 : Fin 1)) ∈ triFam := by
    intro τ hτ
    simp only [F3, mem_insert, mem_singleton] at hτ
    rcases hτ with rfl | rfl | rfl | rfl <;> decide
  exact hasDecomp_map p (fun _ => (0 : Fin 1)) F3 triFam hmap hE

/-- A cleanup covering all internal edges gives a proper colouring of its
residual; no recognition or new partition is assumed. -/
def residualColouring (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (Q : Finset (Sym2 V))
    (hcover : ∀ u v, G.Adj u v → p u = p v → s(u, v) ∈ Q) :
    (G.deleteEdges (Q : Set (Sym2 V))).Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk p fun {u v} h hsame => h.2 (by
    exact ⟨hcover u v h.1 hsame, h.1.ne⟩)

theorem even_residual (G : SimpleGraph V) [DecidableRel G.Adj]
    (Q : Finset (Sym2 V)) (hQ : Q ⊆ G.edgeFinset)
    (hdec : HasDecomp part1 triFam Q)
    (hdiv : IsIntDiv part1 triFam G.edgeFinset) :
    ∀ v, Even ((G.deleteEdges (Q : Set (Sym2 V))).degree v) := by
  have hd := isIntDiv_sdiff_of_hasDecomp hdiv hdec hQ
  have hd' : IsIntDiv part1 triFam
      (G.deleteEdges (Q : Set (Sym2 V))).edgeFinset := by
    simpa only [SimpleGraph.edgeFinset_deleteEdges] using hd
  have he := (isIntDiv_part1_iff _
    (fun _ he => (G.deleteEdges (Q : Set (Sym2 V))).not_isDiag_of_mem_edgeFinset he)).mp hd'
  intro v
  simpa only [FourColourStabilityStage84.incident_edgeFinset] using he.2 v

/-- A uniform consumer of a physical cleanup packing. Its output is a
decomposition of the original edge set, not only the four-partite residual.
The balances here are intermediate obligations discharged by a quota producer. -/
theorem decomposition_of_cleanup :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 / 16 ∧ ∃ N : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W], N ≤ Fintype.card W →
        ∀ (G : SimpleGraph W) [DecidableRel G.Adj] (p : W → Fin 4)
          (Q : Finset (Sym2 W)),
          (3 / 4 : ℝ) * Fintype.card W ≤ (G.minDegree : ℝ) →
          IsIntDiv part1 triFam G.edgeFinset →
          Q ⊆ G.edgeFinset → HasDecomp part1 triFam Q →
          DegBounded Q (eps * Fintype.card W) →
          (∀ u v, G.Adj u v → p u = p v → s(u, v) ∈ Q) →
          (edgeVec p (G.edgeFinset \ Q) 0 1 + edgeVec p (G.edgeFinset \ Q) 2 3 =
            edgeVec p (G.edgeFinset \ Q) 0 2 + edgeVec p (G.edgeFinset \ Q) 1 3) →
          (edgeVec p (G.edgeFinset \ Q) 0 1 + edgeVec p (G.edgeFinset \ Q) 2 3 =
            edgeVec p (G.edgeFinset \ Q) 0 3 + edgeVec p (G.edgeFinset \ Q) 1 2) →
          HasDecomp part1 triFam G.edgeFinset := by
  obtain ⟨eps, heps, heps1, N, hN⟩ :=
    FourColourConsumerStage84.margin_four_colour_decomposition
  refine ⟨eps, heps, heps1, max N 1, ?_⟩
  intro W _ _ hW G _ p Q hmin hdiv hQ hdec hdeg hcover hbal1 hbal2
  classical
  let J := G.deleteEdges (Q : Set (Sym2 W))
  let c : J.Coloring (Fin 4) := residualColouring G p Q hcover
  have hc : (c : W → Fin 4) = p := rfl
  have hnonempty : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  let : Nonempty W := hnonempty
  have hminJ : (3 / 4 - eps) * Fintype.card W ≤ (J.minDegree : ℝ) := by
    obtain ⟨v, hv⟩ := J.exists_minimal_degree_vertex
    rw [hv]
    exact SparseDeletionDegree.minDegree_delete G Q (3 / 4) eps
      (fun w => hmin.trans (by exact_mod_cast G.minDegree_le_degree w)) hdeg v
  have heven := even_residual G Q hQ hdec hdiv
  have hb1 : edgeVec c J.edgeFinset 0 1 + edgeVec c J.edgeFinset 2 3 =
      edgeVec c J.edgeFinset 0 2 + edgeVec c J.edgeFinset 1 3 := by
    rw [hc]
    simpa only [J, SimpleGraph.edgeFinset_deleteEdges] using hbal1
  have hb2 : edgeVec c J.edgeFinset 0 1 + edgeVec c J.edgeFinset 2 3 =
      edgeVec c J.edgeFinset 0 3 + edgeVec c J.edgeFinset 1 2 := by
    rw [hc]
    simpa only [J, SimpleGraph.edgeFinset_deleteEdges] using hbal2
  obtain ⟨D, hD, _⟩ := hN W (le_of_max_le_left hW) J c hminJ heven hb1 hb2
  have hres : HasDecomp part1 triFam (G.edgeFinset \ Q) := by
    simpa only [J, SimpleGraph.edgeFinset_deleteEdges] using ordinary_of_F3 c ⟨D, hD⟩
  simpa only [union_sdiff_of_subset hQ] using hdec.union hres disjoint_sdiff

end PartitionedTriangleAbsorption.CleanupConsumerStage140
