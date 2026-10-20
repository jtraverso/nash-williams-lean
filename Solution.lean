/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib
import RequestProject.NW18.PaperIIAssembly
import RequestProject.Fractional.Final
import RequestProject.FracStab.Main

/-!
# Proofs of the statements in `Challenge.lean`

The definitions `NashWilliams.IsTriangle`, `IsTriangleDecomposition`, `HasTriangleDecomposition`,
`IsTriangleDivisible`, `IsFractionalTriangleDecomposition` and `HasFractionalTriangleDecomposition`
are those of `RequestProject/NashWilliamsBasic.lean`, and `NashWilliams18.cutSize` and
`IsExtremal` those of `RequestProject/NW18/Defs.lean`; they are reproduced verbatim in
`Challenge.lean`.

The main theorem is `NashWilliams18.PaperI.nash_williams_via_paperII`
(`RequestProject/NW18/PaperIIAssembly.lean`), which follows Delcourt–Postle's division into
extremal and non-extremal cases: the extremal residuals are decomposed with the typed absorption
inputs `PaperII.theorem146_F0`, `theorem147_F1` and `theorem147_F2` (Paper II of the series,
developed under `PartitionedTriangleAbsorption/`), and the non-extremal case with a protected
covering-round argument (`roundUnivSpec124_holds`), without assuming Delcourt–Postle's Theorem
13.16. The fractional threshold is `NashWilliams.Frac.exists_fractional_weights`
(`RequestProject/Fractional/Final.lean`), by a dual discharging argument and Farkas' lemma, and
fractional stability is `NashWilliams.Frac.theorem_1_6_proof` (`RequestProject/FracStab/Main.lean`).
-/

namespace NashWilliamsTheorem

open Finset

/-- **The Nash–Williams theorem for large graphs (Delcourt–Postle, Theorem 1.8).** Every
sufficiently large triangle-divisible graph with `3 n ≤ 4 δ(G)` has a triangle decomposition. -/
theorem nash_williams :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
          NashWilliams.HasTriangleDecomposition G :=
  NashWilliams18.PaperI.nash_williams_via_paperII

/-- **The fractional threshold (Delcourt–Postle, Theorem 1.4).** Every finite simple graph with
`3 n ≤ 4 δ(G)` has a fractional triangle decomposition. -/
theorem fractional_nash_williams {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
    ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
      ∀ u v, G.Adj u v → ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t = 1 :=
  NashWilliams.Frac.exists_fractional_weights G hδ

/-- **Fractional stability (Delcourt–Postle, Theorem 1.6), with an order threshold.** There is
`σ₀ > 0` such that for every `0 < σ ≤ σ₀` there are `ε > 0` and `n₀` such that every graph on
`n ≥ n₀` vertices with `δ(G) ≥ (3/4 − ε) n` either has a fractional triangle decomposition or is
`σ`-extremal. -/
theorem fractional_stability :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W] (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
        n₀ ≤ Fintype.card W → (3 / 4 - ε) * (Fintype.card W : ℝ) ≤ (Gr.minDegree : ℝ) →
        ¬ NashWilliams.HasFractionalTriangleDecomposition Gr →
        NashWilliams18.IsExtremal σ Gr :=
  NashWilliams.Frac.theorem_1_6_proof

end NashWilliamsTheorem
