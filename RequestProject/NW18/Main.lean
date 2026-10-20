/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Theorem124
import RequestProject.NW18.Case128.Main
import RequestProject.NW18.Cases

/-!
# Theorem 1.8 (Nash-Williams' Conjecture) from the branch theorems

The case analysis of §12.2 of the paper: Theorem 1.8 follows from Theorems 12.4–12.8.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma IsClose.mono {α α' : ℝ} (h : α ≤ α') {G : SimpleGraph V} [DecidableRel G.Adj]
    {W : Type*} [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    (hc : IsClose α G H) : IsClose α' G H := by
  obtain ⟨e, he⟩ := hc
  exact ⟨e, he.trans (mul_le_mul_of_nonneg_right h (sq_nonneg _))⟩

lemma IsCloseToExtremal.mono {α α' : ℝ} (h : α ≤ α') {G : SimpleGraph V}
    [DecidableRel G.Adj] (hc : IsCloseToExtremal α G) : IsCloseToExtremal α' G := by
  rcases hc with hc | hc | hc
  · exact Or.inl (hc.mono h)
  · exact Or.inr (Or.inl (hc.mono h))
  · exact Or.inr (Or.inr (hc.mono h))

lemma IsExtremal.mono {σ σ' : ℝ} (h : σ ≤ σ') {G : SimpleGraph V} [DecidableRel G.Adj]
    (hx : IsExtremal σ G) : IsExtremal σ' G := by
  obtain ⟨h1, S, h2⟩ := hx
  refine ⟨?_, S, le_trans ?_ h2⟩
  · refine le_trans ?_ (le_trans h1 ?_)
    · exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    · exact_mod_cast card_le_card (monotone_filter_right _ fun v _ hv =>
        le_trans hv (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)))
  · have : 0 ≤ (Fintype.card V : ℝ) ^ 2 := sq_nonneg _
    nlinarith

/-- **Theorem 1.8 (Nash-Williams' Conjecture), from the four open branch theorems.**
There is `N` such that every `K₃`-divisible graph `G` on `n ≥ N` vertices with
`δ(G) ≥ 3n/4` has a triangle decomposition, **provided** the four specialised decomposition
theorems used by the branches hold:
* `h124 : Theorem1316K3Statement` (Theorem 13.16 for `K₃` on hosts with `δ ≥ 3n/4`; branch (1),
  Theorem 12.4),
* `h146 : Theorem146Statement` (Theorem 14.6, idealized `F₀`-hosts; branch (2), Theorem 12.5),
* `h147F1 : Theorem147F1Statement` (Theorem 14.7 for `F₁`; branch (3), Theorem 12.6),
* `h147F2 : Theorem147F2Statement` (Theorem 14.7 for `F₂`; branch (4), Theorem 12.7).

Branch (5) (Theorem 12.8) is proved unconditionally.  The global interface
`Theorem1316Statement` is **not** a premise here; it implies all four premises
(`nash_williams_of_theorem_13_16`).  This is a conditional theorem: none of the four premises
is proved in this project.  The proof is the case analysis of §12.2 of the paper. -/
theorem nash_williams_of_branch_theorems (h124 : Theorem1316K3Statement)
    (h146 : Theorem146Statement) (h147F1 : Theorem147F1Statement)
    (h147F2 : Theorem147F2Statement) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨α₁, hα₁, n₁, h₁⟩ := theorem_12_6_of_147 h147F1
  obtain ⟨α₂, hα₂, n₂, h₂⟩ := C127.theorem_12_7_of_147 h147F2
  obtain ⟨α₃, hα₃, n₃, h₃⟩ := theorem_12_8
  set α := min α₁ (min α₂ α₃) with hα
  have hαpos : 0 < α := lt_min hα₁ (lt_min hα₂ hα₃)
  obtain ⟨β, hβ, n₄, h₄⟩ := theorem_12_5_of_146 h146 α hαpos
  obtain ⟨β₀, hβ₀, h₅⟩ := theorem_12_4_of_K3 h124
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

/-- **Theorem 1.8 (Nash-Williams' Conjecture), assuming Theorem 13.16** (the global interface
`h1316 : Theorem1316Statement`).  Kept for compatibility; it is derived from
`nash_williams_of_branch_theorems`, whose four premises are specialisations of `h1316`.
Note: the arbitrary-host interface `Theorem1316Statement` (aggregated label divisibility) has
been reported to admit a physical-lattice counterexample (see `NW18_BRANCH_LEDGER.md`); if so,
this theorem is vacuous, and `nash_williams_of_branch_theorems` is the meaningful conditional
form. -/
theorem nash_williams_of_theorem_13_16 (h1316 : Theorem1316Statement) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_branch_theorems (theorem1316K3_of_theorem1316 h1316) (theorem_14_6 h1316)
    (theorem_14_7_F1 h1316) (theorem_14_7_F2 h1316)

end NashWilliams18
