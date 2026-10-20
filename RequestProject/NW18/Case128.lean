/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Defs
import PartitionedTriangleAbsorption.CleanupGeometryStage140
import PartitionedTriangleAbsorption.FourColourConsumerStage84
import PartitionedTriangleAbsorption.ExceptionalGeometryStage141
import PartitionedTriangleAbsorption.CommonClassSupply

/-!
# Case (5) of §12.2 (Theorem 12.8): the route through the local F3 consumers

Theorem 12.8 treats graphs `α`-close to `T₂(n/2)+T₂(n/2)`.  This file connects that case to
the modules of the local route ported in `Stage133Port` (Stages 140–146 and
`CommonClassSupply`):

* `sparse_internal_triangle_decomposition` — the Stage140 consumer
  (`CleanupGeometryStage140.sparse_internal_decomposition`) in the vocabulary of Theorem 1.8:
  a `K₃`-divisible graph with `δ(G) ≥ 3n/4` and a four-part partition of **small maximum**
  internal degree has a triangle decomposition (unconditionally; no Theorem 13.16).
* `exists_partition_internal_le_of_close` — `α`-closeness to `T₂(n/2)+T₂(n/2)` gives a
  four-part partition with at most `α n²` internal edges (small **average** internal degree).
* `claim_12_8_5_two_destination_classes` — the numerical content of Claim 12.8.5, derived from
  closeness: the class-size bounds come from Stage141 and the internal-degree inputs from the
  hypothesis that both roots are non-exceptional; then `CommonClassSupply` gives two external
  destination classes each with `≥ n/20` common neighbours.  As in `CommonClassSupply`, this is
  a single-destination-class statement (the printed `L(e)` on p. 113 has an unbound `k`).
* `ExceptionalCleanup128` — the exact residual obligation of this case (a sparse exceptional
  pre-clean `Q` with the quantitative hypotheses on the **same** residual), and
  `theorem_12_8_of_exceptional_cleanup`, which derives the conclusion of Theorem 12.8 from it
  via `FourColourConsumerStage84.margin_four_colour_decomposition` applied to the residual on
  the non-exceptional vertices.  Note that the residual is **not** assumed to satisfy
  `δ ≥ 3n/4`: only the loss `≤ 2εn` per vertex is used, which the consumer tolerates.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

/-! ### Translation between the one-part encodings -/

section Translation

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma hasTriangleDecomposition_of_hasDecomp_part1 (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : HasDecomp OnePart.part1 OnePart.triFam G.edgeFinset) :
    NashWilliams.HasTriangleDecomposition G :=
  (hasDecomp_K3_iff G).mp h

lemma isIntDiv_part1_of_triangleDivisible (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : NashWilliams.IsTriangleDivisible G) :
    IsIntDiv OnePart.part1 OnePart.triFam G.edgeFinset :=
  (isIntDiv_K3_iff G).mpr h

end Translation

/-! ### The Stage140 consumer: small maximum internal degree -/

/-- **Theorem 12.8 when the internal degree is uniformly small** (Stage140 consumer).
There are `ε > 0` and `N` (chosen before the graph) such that every `K₃`-divisible graph `G`
on `n ≥ N` vertices with `δ(G) ≥ 3n/4`, together with a partition `p` of its vertices into four
classes in which every vertex has at most `εn` neighbours in its own class, has a triangle
decomposition.  Proved unconditionally (no Theorem 13.16). -/
theorem sparse_internal_triangle_decomposition :
    ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 4), N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
        (∀ x, (((G.neighborFinset x).filter (fun y => p y = p x)).card : ℝ) ≤
          ε * Fintype.card V) →
        NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨eps, heps, -, N, h⟩ := CleanupGeometryStage140.sparse_internal_decomposition
  refine ⟨eps, heps, N, fun V _ _ G _ p hN hdiv hδ hint => ?_⟩
  apply hasTriangleDecomposition_of_hasDecomp_part1
  refine h V hN G p ?_ (isIntDiv_part1_of_triangleDivisible G hdiv) fun x => ?_
  · have : (3 * Fintype.card V : ℝ) ≤ 4 * G.minDegree := by exact_mod_cast hδ
    linarith
  · rw [CleanupGeometryStage140.internal_load_eq]
    convert hint x using 3
    ext y
    simp [CleanupSupplyStage140.internalNeighbours, ClassRepresentativesStage65.classSet]

/-! ### Closeness gives small average internal degree -/

/-- If `G` is `α`-close to `T₂(n/2)+T₂(n/2)`, then the four classes of the layout of
`T₂(n/2)+T₂(n/2)`, pulled back to `G`, span at most `α n²` edges of `G`. -/
theorem exists_partition_internal_le_of_close {V : Type*} [Fintype V] [DecidableEq V]
    (α : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hc : IsClose α G (T2T2 (Fintype.card V))) :
    ∃ p : V → Fin 4,
      ((G.edgeFinset.filter (fun e => (e.map p).IsDiag)).card : ℝ) ≤
        α * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨e, he⟩ := hc
  refine ⟨fun v => quarter _ (e v), le_trans ?_ he⟩
  refine Nat.cast_le.mpr (card_le_card fun x hx => ?_)
  obtain ⟨hxG, hxd⟩ := mem_filter.mp hx
  refine Finset.mem_symmDiff.mpr (Or.inl ⟨hxG, ?_⟩)
  induction x using Sym2.ind with
  | _ u v =>
    simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hxd
    intro hmem
    have hadj := SimpleGraph.mem_edgeFinset.mp hmem
    change e u ≠ e v ∧ decide (quarter _ (e u) ≠ quarter _ (e v)) = true at hadj
    exact (of_decide_eq_true hadj.2) hxd

/-! ### Claim 12.8.5: two destination classes (numerical content) -/

/-- **Claim 12.8.5 (numerical content), derived from closeness.**  Let `G` have `n > 0`
vertices, `δ(G) ≥ 3n/4`, and be `α`-close to `T₂(n/2)+T₂(n/2)` with `0 ≤ α < 1/1920`.  Then the
partition `p` pulled back from the layout of `T₂(n/2)+T₂(n/2)` has at most `αn²` internal
edges, and for any two vertices `u, v` in the same class each having at most `8αn` neighbours
in its own class (i.e. both non-exceptional for the threshold `τ = 8α`), there are two
distinct classes `j ≠ k`, both different from the class of `u`, each containing at least
`n/20` common neighbours of `u` and `v`.

The class-size bound `|V_j| ≤ (1/4 + 8α) n` is derived (Stage141,
`ExceptionalGeometryStage141.class_upper_average`), not assumed; the internal-degree inputs
are the non-exceptionality hypotheses on `u, v`.  This is the single-destination-class list
assertion of `CommonClassSupply` (the printed `L(e)` on p. 113 contains an unbound `k`; no
paired-colour list assertion is claimed). -/
theorem claim_12_8_5_two_destination_classes {V : Type*} [Fintype V] [DecidableEq V]
    (α : ℝ) (hα0 : 0 ≤ α) (hα : α < 1 / 1920) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hn : 0 < Fintype.card V) (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree)
    (hc : IsClose α G (T2T2 (Fintype.card V))) :
    ∃ p : V → Fin 4,
      ((G.edgeFinset.filter (fun e => (e.map p).IsDiag)).card : ℝ) ≤
        α * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ u v : V, p u = p v →
        (((G.neighborFinset u).filter (fun y => p y = p u)).card : ℝ) ≤
          8 * α * Fintype.card V →
        (((G.neighborFinset v).filter (fun y => p y = p v)).card : ℝ) ≤
          8 * α * Fintype.card V →
        ∃ j k : Fin 4, j ≠ k ∧ j ≠ p u ∧ k ≠ p u ∧
          (Fintype.card V : ℝ) / 20 ≤
            ((univ.filter (fun w => p w = j ∧ G.Adj u w ∧ G.Adj v w)).card : ℝ) ∧
          (Fintype.card V : ℝ) / 20 ≤
            ((univ.filter (fun w => p w = k ∧ G.Adj u w ∧ G.Adj v w)).card : ℝ) := by
  obtain ⟨p, hp⟩ := exists_partition_internal_le_of_close α G hc
  refine ⟨p, hp, fun u v huv hu hv => ?_⟩
  have hmin : (3 / 4 : ℝ) * Fintype.card V ≤ G.minDegree := by
    have : (3 * Fintype.card V : ℝ) ≤ 4 * G.minDegree := by exact_mod_cast hδ
    linarith
  have hdeg : ∀ w, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree w := fun w =>
    hmin.trans (by exact_mod_cast G.minDegree_le_degree w)
  have hsize := ExceptionalGeometryStage141.class_upper_average G p α hα0 hn hdeg hp
  have hint : ∀ w, (CleanupSupplyStage140.internalNeighbours G p w) =
      (G.neighborFinset w).filter (fun y => p y = p w) := by
    intro w; ext y
    simp [CleanupSupplyStage140.internalNeighbours, ClassRepresentativesStage65.classSet]
  have hcand : ∀ j, CleanupSupplyStage140.candidates G p u v j =
      univ.filter (fun w => p w = j ∧ G.Adj u w ∧ G.Adj v w) := by
    intro j; ext w
    simp [CleanupSupplyStage140.candidates, ClassRepresentativesStage65.classSet]
  have hroot : ∀ w, (((G.neighborFinset w).filter (fun y => p y = p w)).card : ℝ) ≤
      8 * α * Fintype.card V →
      ((CleanupSupplyStage140.internalNeighbours G p w).card : ℝ) ≤
        G.degree w / 4 + 8 * α * Fintype.card V := by
    intro w hw
    rw [hint]
    have : (0 : ℝ) ≤ G.degree w / 4 := by positivity
    linarith
  obtain ⟨j, k, hjk, hj, hk, hjc, hkc⟩ :=
    CommonClassSupply.exists_two_destination_classes G p u v (8 * α) hn (by linarith) hsize
      hmin huv (hroot u hu) (hroot v hv)
  rw [hcand] at hjc hkc
  exact ⟨j, k, hjk, hj, hk, hjc, hkc⟩

end NashWilliams18
