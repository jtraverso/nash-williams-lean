/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Defs
public import RequestProject.NW18.Case125.Assembly
public import RequestProject.NW18.Case126.Theorem126
public import RequestProject.NW18.Case127.Theorem127

@[expose] public section

/-!
# Theorem 1.8: the ingredients from Parts II and III of the paper

Statements, as in the paper, of the results from which Theorem 1.8 is assembled in §12.2:

* `theorem_12_5` … `theorem_12_7` — the extremal cases (2)–(4) of the proof (case (5),
  Theorem 12.8, is in `Case128/Main.lean`).

The non-extremal case, Theorem 12.4, is *derived* in `Theorem124.lean` from Theorem 13.16,
Theorem 2.6 (itself derived in `Theorem26Proof.lean` from Theorem 1.6 and Lemma 11.6) and
Lemma 14.4 (reduced in `HingeCount.lean` to a count of explicit hinge configurations), and
Theorem 1.8 is derived in `Main.lean`.

**Status:** `theorem_12_5`, `theorem_12_6` and `theorem_12_7` are proved from the hypothesis
`h1316` (free of `sorryAx`).  They are now corollaries of the versions with specialised
premises, `theorem_12_5_of_146` (`Theorem146Statement`), `theorem_12_6_of_147`
(`Theorem147F1Statement`) and `C127.theorem_12_7_of_147` (`Theorem147F2Statement`), which are
the ones used by `nash_williams_of_branch_theorems`.  None of these premises is proved.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

/- `IsCloseToExtremal` (unchanged) now lives in `RequestProject/NW18/Defs.lean`, so that the
proof of Theorem 12.5 (in `RequestProject/NW18/Case125/`) can use it and be imported here. -/

/-- **Theorem 12.5** (case (2): extremal, but not close to the three extremal graphs).
Proved in `RequestProject/NW18/Case125/Assembly.lean` (`theorem_12_5_proof`) from Theorem 13.16
(`h1316`), following §15.3 of the paper; it does not depend on `sorryAx`. -/
theorem theorem_12_5 (h1316 : Theorem1316Statement) :
    ∀ α : ℝ, 0 < α → ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsExtremal β G → ¬ IsCloseToExtremal α G →
        NashWilliams.HasTriangleDecomposition G :=
  theorem_12_5_proof h1316

/-- **Theorem 12.6** (case (3): close to `T̄₂(n/2)+T̄₂(n/2)`, family `F₁`).
Proved in `RequestProject/NW18/Case126/Theorem126.lean` (`theorem_12_6_proof`) from Theorem 13.16
(`h1316`), following §15.5 of the paper; it does not depend on `sorryAx`. -/
theorem theorem_12_6 (h1316 : Theorem1316Statement) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2bT2b (Fintype.card V)) →
        NashWilliams.HasTriangleDecomposition G :=
  theorem_12_6_proof h1316

/-- **Theorem 12.7** (case (4): close to `T̄₂(n/2)+T₂(n/2)`, family `F₂`).
Proved in `RequestProject/NW18/Case127/Theorem127.lean` (`C127.theorem_12_7_proof`) from
Theorem 13.16 (`h1316`), following §15.6 of the paper; it does not depend on `sorryAx`. -/
theorem theorem_12_7 (h1316 : Theorem1316Statement) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsClose α G (T2bT2 (Fintype.card V)) →
        NashWilliams.HasTriangleDecomposition G :=
  C127.theorem_12_7_proof h1316

/- **Theorem 12.8** (case (5): close to `T₂(n/2)+T₂(n/2)`, family `F₃`) has moved to
`RequestProject/NW18/Case128/Main.lean` (`theorem_12_8`), where it is derived from the
F3 consumers of the local route and the residual obligation `ExceptionalCleanup128`
(stated in `Case128Reduction.lean` and proved as `exceptional_cleanup_128`).
Its statement there is the one formerly stated here, without the hypothesis `h1316`
(Theorem 13.16 is not used in this case). -/

end NashWilliams18
