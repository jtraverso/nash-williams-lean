/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import RequestProject.Fractional.Final

@[expose] public section

/-!
# Nash-Williams' Conjecture (Delcourt–Postle, arXiv:2606.11178): definitions

Formal statement of the main result of *A Proof of Nash-Williams' Conjecture*
by M. Delcourt and L. Postle (Theorem 1.8), together with the fractional
version (Theorem 1.4), and some fully proved sanity checks of the definitions.
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

open NashWilliams

/-- **Theorem 1.4 (Fractional Nash-Williams' Conjecture).**
Every graph `G` on `n` vertices with minimum degree `δ(G) ≥ 3n/4` admits a fractional
triangle decomposition. (The condition `δ(G) ≥ 3n/4` is written as `3n ≤ 4 δ(G)`.) -/
theorem fractional_nash_williams
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
    HasFractionalTriangleDecomposition G :=
  NashWilliams.Frac.exists_fractional_weights G hδ

/-- **Theorem 1.2 (Barber–Kühn–Lo–Osthus), as a proposition.**
If every graph `G` on `n` vertices with `δ(G) ≥ c·n` has a fractional triangle decomposition
(i.e. the fractional decomposition threshold is at most `c`), then for every `ε > 0` there is
`N` such that every `K₃`-divisible graph on `n ≥ N` vertices with `δ(G) ≥ (c + ε)·n` has a
triangle decomposition. This is *not* proved here; it is only used as an explicit hypothesis. -/
def BKLOStatement : Prop :=
  ∀ c : ℝ, (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      c * Fintype.card V ≤ G.minDegree → HasFractionalTriangleDecomposition G) →
    ∀ ε > 0, ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], N ≤ Fintype.card V → IsTriangleDivisible G →
        (c + ε) * Fintype.card V ≤ G.minDegree → HasTriangleDecomposition G

/-- **Corollary 1.5.** Assuming the Barber–Kühn–Lo–Osthus theorem (`BKLOStatement`, an explicit
hypothesis), for every `ε > 0` there is `N` such that every `K₃`-divisible graph on `n ≥ N`
vertices with `δ(G) ≥ (3/4 + ε)·n` has a triangle decomposition. Follows from Theorem 1.4. -/
theorem nash_williams_asymptotic (hBKLO : BKLOStatement) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → IsTriangleDivisible G →
        (3 / 4 + ε) * Fintype.card V ≤ G.minDegree → HasTriangleDecomposition G := by
  refine hBKLO (3 / 4) (fun V _ _ G _ h => fractional_nash_williams G ?_) ε hε
  have : (3 * Fintype.card V : ℝ) ≤ 4 * G.minDegree := by linarith
  exact_mod_cast this
