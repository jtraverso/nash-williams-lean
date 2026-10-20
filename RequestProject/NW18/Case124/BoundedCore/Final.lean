/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.BoundedCore.CoreAbsorber
import RequestProject.NW18.Case124.BoundedCore.RoundTransport

/-!
# Theorem 1.8 from the single protected cover-down round

With the proved `coreAbsorberSpec124`, `vortexSpec124`, `theorem146Statement_holds` and the
proved iteration `vortexCoverSpec124_of_round`, the only remaining input of Theorem 1.8 is the
one-round cover-down `RoundSpec124`.
-/

namespace NashWilliams18

/-- **Branch 12.4 from one protected round** (proved assembly). -/
theorem branch124_of_round (hR : RoundSpec124) : Branch124Statement :=
  branch124_of_bounded_core coreAbsorberSpec124 (vortexCoverSpec124_of_round hR)

/-- **Theorem 1.8 from one protected round** (proved assembly; all other inputs are proved). -/
theorem nash_williams_of_round (hR : RoundSpec124) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_bounded_core coreAbsorberSpec124 (vortexCoverSpec124_of_round hR)

/-- **Theorem 1.8 from the protected round on a whole vertex type** (proved assembly; the
transport to induced parents is `roundSpec124_of_univ`). -/
theorem nash_williams_of_round_univ (hR : RoundUnivSpec124) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_round (roundSpec124_of_univ hR)

end NashWilliams18
