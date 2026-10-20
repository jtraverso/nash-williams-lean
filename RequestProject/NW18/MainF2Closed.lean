/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.MainF1Closed
import PartitionedTriangleAbsorption.BlowupB.KeevashF12Closed

/-!
# Theorem 14.7 for `F₂` and branch 12.7, unconditionally

`PartitionedTriangleAbsorption.BlowupB.theorem147_F2` is the supplied proof (Stage 257 delivery,
ported to Lean 4.28 / Mathlib `v4.28.0` in `Stage133Port/PartitionedTriangleAbsorption/BlowupB`).
Its statement uses `IsIdealizedNW`, a verbatim copy of `IsIdealizedT`; the two are definitionally
equal, and the kernel checks the link below (no textual comparison is relied upon).

With `theorem_14_7_F2_unconditional`, Theorem 1.8 follows from the two remaining branch theorems
`Theorem1316K3Statement` (12.4) and `Theorem146Statement` (12.5).
-/

namespace NashWilliams18

/-- **Theorem 14.7 for `F₂`, unconditionally** (from the ported padded Keevash proof). -/
theorem theorem_14_7_F2_unconditional : Theorem147F2Statement := by
  obtain ⟨ε, hε, n₀, h⟩ := PartitionedTriangleAbsorption.BlowupB.theorem147_F2
  exact ⟨ε, hε, n₀, fun V _ _ p G _ hn hint hid => h V p G hn hint hid⟩

/-- **Branch (4), Theorem 12.7, unconditionally.** -/
theorem theorem_12_7_unconditional :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2bT2 (Fintype.card V)) →
        NashWilliams.HasTriangleDecomposition G :=
  C127.theorem_12_7_of_147 theorem_14_7_F2_unconditional

/-- **Theorem 1.8 from the two remaining branch theorems** (12.4 and 12.5). -/
theorem nash_williams_of_two_branches (h124 : Theorem1316K3Statement)
    (h146 : Theorem146Statement) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_remaining_branches h124 h146 theorem_14_7_F2_unconditional

end NashWilliams18
