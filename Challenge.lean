/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib

/-!
# The Nash–Williams triangle-decomposition theorem

* `NashWilliamsTheorem.nash_williams`: **the Nash–Williams theorem for large graphs
  (Delcourt–Postle, Theorem 1.8).** There is `N` such that every finite simple graph on
  `n ≥ N` vertices that is triangle-divisible (`3 ∣ e(G)` and every degree even) and has minimum
  degree `δ(G) ≥ 3n/4` (stated as `3 n ≤ 4 δ(G)`) has a triangle decomposition: a family of
  triangles of `G` such that every edge of `G` lies in exactly one of them.
* `NashWilliamsTheorem.fractional_nash_williams`: **the fractional threshold (Delcourt–Postle,
  Theorem 1.4).** Every finite simple graph with `3 n ≤ 4 δ(G)` has a fractional triangle
  decomposition: nonnegative real weights on vertex sets such that, for every edge, the weights
  of the triangles containing it sum to one. Neither divisibility nor large order is assumed.
* `NashWilliamsTheorem.fractional_stability`: **fractional stability (Delcourt–Postle,
  Theorem 1.6), with an order threshold.** Some `σ₀ > 0` works so that for every
  `0 < σ ≤ σ₀` there are `ε > 0` and `n₀`: every graph on `n ≥ n₀` vertices with
  `δ(G) ≥ (3/4 − ε) n` has a fractional triangle decomposition or is `σ`-extremal
  (`NashWilliams18.IsExtremal`: at least `(1 − σ) n` vertices have degree at most
  `(3/4 + σ) n`, and some cut has at least `(1 − σ) n²/4` edges).

The definitions below are reproduced verbatim, with the same names, from
`RequestProject/NashWilliamsBasic.lean` (namespace `NashWilliams`) and
`RequestProject/NW18/Defs.lean` (namespace `NashWilliams18`) of the formalization.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

namespace NashWilliams

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A *triangle* of `G` is a 3-clique, i.e. a 3-element set of pairwise adjacent vertices. -/
abbrev IsTriangle (G : SimpleGraph V) (t : Finset V) : Prop := G.IsNClique 3 t

/-- A *triangle decomposition* (`K₃`-decomposition) of `G`: a family `D` of triangles of `G`
such that every edge of `G` lies in exactly one triangle of `D`
(equivalently, the edge sets of the triangles of `D` partition `E(G)`). -/
def IsTriangleDecomposition (G : SimpleGraph V) (D : Finset (Finset V)) : Prop :=
  (∀ t ∈ D, IsTriangle G t) ∧ ∀ u v, G.Adj u v → ∃! t, t ∈ D ∧ u ∈ t ∧ v ∈ t

/-- `G` admits a triangle decomposition. -/
def HasTriangleDecomposition (G : SimpleGraph V) : Prop :=
  ∃ D, IsTriangleDecomposition G D

/-- `G` is `K₃`-divisible: `3 ∣ e(G)` and every vertex has even degree. -/
def IsTriangleDivisible (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  3 ∣ G.edgeFinset.card ∧ ∀ v, Even (G.degree v)

/-- A *fractional triangle decomposition* of `G`: a non-negative weighting of the triangles
of `G` such that, for every edge, the total weight of the triangles containing it is `1`. -/
def IsFractionalTriangleDecomposition (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧
    ∀ u v, G.Adj u v → ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t = 1

/-- `G` admits a fractional triangle decomposition. -/
def HasFractionalTriangleDecomposition (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ w, IsFractionalTriangleDecomposition G w

end NashWilliams

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Number of edges of `G` with exactly one end in `S` (the cut `(S, V ∖ S)`). -/
def cutSize (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (G.edgeFinset.filter (fun e => ∃ u v, e = s(u, v) ∧ u ∈ S ∧ v ∉ S)).card

/-- **`σ`-extremal** (Definition 12.2): (i) at least `(1 - σ) n` vertices have degree at most
`(3/4 + σ) n`, and (ii) the maximum cut of `G` has at least `(1 - σ) n² / 4` edges. -/
def IsExtremal (σ : ℝ) (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  (1 - σ) * Fintype.card V ≤
      ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)).card : ℝ) ∧
    ∃ S : Finset V, (1 - σ) * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (cutSize G S : ℝ)

end NashWilliams18

namespace NashWilliamsTheorem

open Finset

/-- **The Nash–Williams theorem for large graphs (Delcourt–Postle, Theorem 1.8).** Every
sufficiently large triangle-divisible graph with `3 n ≤ 4 δ(G)` has a triangle decomposition. -/
theorem nash_williams :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
          NashWilliams.HasTriangleDecomposition G := by
  sorry

/-- **The fractional threshold (Delcourt–Postle, Theorem 1.4).** Every finite simple graph with
`3 n ≤ 4 δ(G)` has a fractional triangle decomposition. -/
theorem fractional_nash_williams {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
    ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
      ∀ u v, G.Adj u v → ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t = 1 := by
  sorry

/-- **Fractional stability (Delcourt–Postle, Theorem 1.6), with an order threshold.** There is
`σ₀ > 0` such that for every `0 < σ ≤ σ₀` there are `ε > 0` and `n₀` such that every graph on
`n ≥ n₀` vertices with `δ(G) ≥ (3/4 − ε) n` either has a fractional triangle decomposition or is
`σ`-extremal. -/
theorem fractional_stability :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W] (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
        n₀ ≤ Fintype.card W → (3 / 4 - ε) * (Fintype.card W : ℝ) ≤ (Gr.minDegree : ℝ) →
        ¬ NashWilliams.HasFractionalTriangleDecomposition Gr →
        NashWilliams18.IsExtremal σ Gr := by
  sorry

end NashWilliamsTheorem
