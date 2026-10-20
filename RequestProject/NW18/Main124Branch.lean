/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.MainF2Closed

@[expose] public section

/-!
# Final consumer taking the exact branch statement 12.4

`Theorem1316K3Statement` (Theorem 13.16 for `K₃` on hosts with `δ ≥ 3n/4`) has **no**
non-extremality premise, whereas the robust transport results (Stage 263–268) use exactly that
premise.  The old consumer `nash_williams_of_branch_theorems` only used its `K₃` premise to obtain
the conclusion of `theorem_12_4_of_K3`.  Here the premise is replaced by that conclusion itself,
`Branch124Statement`.  This file does **not** prove `Branch124Statement`.
-/

namespace NashWilliams18

/-- **The exact statement of branch (1), Theorem 12.4** (the conclusion of
`theorem_12_4_of_K3`): there is `β₀ > 0` such that for every `0 < β ≤ β₀` there is `n₀`, and every
triangle-divisible `G` on `n ≥ n₀` vertices with `δ(G) ≥ 3n/4` that is not `β`-extremal has a
triangle decomposition. -/
def Branch124Statement : Prop :=
  ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
      3 * Fintype.card V ≤ 4 * G.minDegree → ¬ IsExtremal β G →
      NashWilliams.HasTriangleDecomposition G

/-- The old premise implies the new one (so the new consumer is at least as general). -/
theorem branch124_of_K3 (h124 : Theorem1316K3Statement) : Branch124Statement :=
  theorem_12_4_of_K3 h124

/-- **Theorem 1.8 from the exact branch statement 12.4 and Theorem 14.6** (branch 12.5);
branches 12.6, 12.7 and 12.8 are the closed, premise-free theorems. -/
theorem nash_williams_of_branch124 (h124 : Branch124Statement) (h146 : Theorem146Statement) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨α₁, hα₁, n₁, h₁⟩ := theorem_12_6_unconditional
  obtain ⟨α₂, hα₂, n₂, h₂⟩ := theorem_12_7_unconditional
  obtain ⟨α₃, hα₃, n₃, h₃⟩ := theorem_12_8
  set α := min α₁ (min α₂ α₃) with hα
  have hαpos : 0 < α := lt_min hα₁ (lt_min hα₂ hα₃)
  obtain ⟨β, hβ, n₄, h₄⟩ := theorem_12_5_of_146 h146 α hαpos
  obtain ⟨β₀, hβ₀, h₅⟩ := h124
  set β' := min β₀ β
  obtain ⟨n₅, h₅⟩ := h₅ β' (lt_min hβ₀ hβ) (min_le_left _ _)
  refine ⟨max (max n₁ n₂) (max n₃ (max n₄ n₅)), fun V _ _ G _ hn hdiv hδ => ?_⟩
  have hn₁ : n₁ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₃ : n₃ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₄ : n₄ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₅ : n₅ ≤ Fintype.card V := le_trans (by omega) hn
  by_cases c3 : IsClose α G (T2T2 (Fintype.card V))
  · exact h₃ V G hn₃ hdiv hδ (c3.mono (le_trans (min_le_right _ _) (min_le_right _ _)))
  by_cases c2 : IsClose α G (T2bT2 (Fintype.card V))
  · exact h₂ V G hn₂ hdiv hδ (c2.mono (le_trans (min_le_right _ _) (min_le_left _ _)))
  by_cases c1 : IsClose α G (T2bT2b (Fintype.card V))
  · exact h₁ V G hn₁ hdiv hδ (c1.mono (min_le_left _ _))
  have hnc : ¬ IsCloseToExtremal α G := by
    rintro (h | h | h) <;> contradiction
  by_cases hx : IsExtremal β' G
  · exact h₄ V G hn₄ hdiv hδ (hx.mono (min_le_right _ _)) hnc
  · exact h₅ V G hn₅ hdiv hδ hx

end NashWilliams18
