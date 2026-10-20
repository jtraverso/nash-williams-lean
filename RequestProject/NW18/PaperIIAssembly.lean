/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.BlowupPaperInputs
public import RequestProject.NW18.Case124.BoundedCore.Final
public import RequestProject.NW18.Case124.BoundedCore.RoundProducer

@[expose] public section

/-!
# Nash-Williams assembled with the typed blowup inputs of Paper II

This is the canonical completed assembly used by Paper I.
The case analysis is the existing one from `Main124Branch`, with both typed
inputs supplied explicitly by `PaperII`, together with its separate F0 input.
The non-extremal branch and the exceptional cleanup retain their own proofs.
F0 is not asserted to follow from near-complete typed blowups.
-/

namespace NashWilliams18.PaperI

theorem nash_williams_of_paperII_inputs
    (h124 : Branch124Statement) (h146 : Theorem146Statement) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
          NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨α₁, hα₁, n₁, h₁⟩ := theorem_12_6_of_147 PaperII.theorem147_F1
  obtain ⟨α₂, hα₂, n₂, h₂⟩ := C127.theorem_12_7_of_147 PaperII.theorem147_F2
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

/-- Canonical full assembly, using the F0, F1 and F2 inputs of Paper II. -/
theorem nash_williams_via_paperII :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
          NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_paperII_inputs
    (branch124_of_round (roundSpec124_of_univ roundUnivSpec124_holds))
    PaperII.theorem146_F0

end NashWilliams18.PaperI

#print axioms NashWilliams18.PaperI.nash_williams_of_paperII_inputs
#print axioms NashWilliams18.PaperI.nash_williams_via_paperII
