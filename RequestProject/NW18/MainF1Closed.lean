/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Main
import RequestProject.NW18.Case126.VortexF1

/-!
# Theorem 1.8 with the `F₁` branch discharged

`theorem_14_7_F1_of_vortex` (proved, `Case126/VortexF1.lean`) discharges the premise
`Theorem147F1Statement` of `nash_williams_of_branch_theorems`.  The remaining premises are the
three open branch theorems `Theorem1316K3Statement` (12.4), `Theorem146Statement` (12.5) and
`Theorem147F2Statement` (12.7); branch 12.8 is proved unconditionally.  This is still a
conditional theorem; the public `nash_williams` is not closed by it.
-/

namespace NashWilliams18

/-- **Branch (3), Theorem 12.6, unconditionally** (from the proved `F₁` Theorem 14.7). -/
theorem theorem_12_6_unconditional :
    ∃ α > 0, ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj], n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
      3 * Fintype.card V ≤ 4 * G.minDegree →
      IsClose α G (T2bT2b (Fintype.card V)) → NashWilliams.HasTriangleDecomposition G :=
  theorem_12_6_of_147 theorem_14_7_F1_of_vortex

/-- **Theorem 1.8 from the three remaining branch theorems** (12.4, 12.5, 12.7). -/
theorem nash_williams_of_remaining_branches (h124 : Theorem1316K3Statement)
    (h146 : Theorem146Statement) (h147F2 : Theorem147F2Statement) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_branch_theorems h124 h146 theorem_14_7_F1_of_vortex h147F2

end NashWilliams18
