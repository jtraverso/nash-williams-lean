/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.GlobalCaseI

/-!
# The global part of Theorem 10.9, assembled

`global_main`: in the `Setting` (with all small parameters bounded by `r ≤ σ / 4000`), a pair
`f₀ ∈ E₂` of maximal weight `F₀` forces `G` to be `σ`-extremal.  We distinguish whether one side of
the balanced bipartition of `f₀` spans many edges (Case II) or not (Case I).
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- The complement of a balanced bipartition is a balanced bipartition. -/
lemma isBalBip_compl {α : ℝ} {u v : V} {A : Finset V} (hA : IsBalBip G φ α u v A) :
    IsBalBip G φ α u v (cn G u v \ A) := by
  obtain ⟨h1, h2, h3, h4⟩ := hA
  have e : cn G u v \ (cn G u v \ A) = A := Finset.sdiff_sdiff_eq_self h1
  refine ⟨sdiff_subset, h3, by rw [e]; exact h2, ?_⟩
  rw [e, normalCount_comm]
  exact h4

/-- **Global part of Theorem 10.9.** -/
theorem global_main {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {ι σ : ℝ}
    {u0 v0 : V} (hf0 : (u0, v0) ∈ E2 G φ t) (hF0 : F₀ ≤ negW φ (u0, v0))
    (hn1 : 1 ≤ ι * Fintype.card V) (hσ : 4000 * r ≤ σ) (hα2 : α ≤ 2 * r ^ 2)
    (hεr : ε ≤ r) (htr : t ≤ r) (hκr : κ ≤ r) (hsr : s ≤ r) (hζr : ζ ≤ r) (hιr : ι ≤ r)
    (hr1 : r ≤ 1 / 400000) :
    NashWilliams18.IsExtremal σ G := by
  have hF := H.F₀pos
  have hr := H.hr
  have hε0 := H.hε0
  have ht0 := H.ht0
  have hκ0 := H.hκ0
  have hs0 := H.hs
  have hα0 := H.hα0
  have hnpos := card_pos_of_iota hn1
  have hζ : 0 ≤ ζ := by
    have hS : ((SS G φ t F₀ s).card : ℝ) ≤ ζ * Fintype.card V := H.S_le
    by_contra h; push_neg at h
    have : ζ * (Fintype.card V : ℝ) < 0 := mul_neg_of_neg_of_pos h hnpos
    have : (0 : ℝ) ≤ (SS G φ t F₀ s).card := Nat.cast_nonneg _
    linarith
  have hι : 0 < ι := by
    by_contra h; push_neg at h; nlinarith
  have hν : α / (2 * r) ≤ r := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have hν0 : 0 ≤ α / (2 * r) := by positivity
  -- the bipartition of `f₀`
  obtain ⟨A0, hA0⟩ := H.bip _ hf0 (mem_HH_of_E2 G φ (ρ := 1) (by norm_num) hF hf0 (by linarith))
  simp (config := { failIfUnchanged := false }) only at hA0
  set β : ℝ := 40 * r
  have hβ : 0 < β := by positivity
  -- numerical facts
  have hrt : r * t ≤ r * r := mul_le_mul_of_nonneg_left htr hr.le
  have hMb : 1 / 2 - 4 * r ≤ 3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι := by nlinarith
  have hLb : 1 / 2 - 8 * r ≤ (1 / 2 - ε - t - r - 3 * s - κ) - ι := by linarith
  have hcut : (1 - σ) / 4 ≤ ((1 / 2 - ε - t - r - 3 * s - κ) - ι) *
      (3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι) := by
    have h1 : (1 / 2 - 8 * r) * (1 / 2 - 4 * r) ≤ ((1 / 2 - ε - t - r - 3 * s - κ) - ι) *
        (3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι) :=
      mul_le_mul hLb hMb (by linarith) (by linarith)
    nlinarith
  by_cases hA : β * (Fintype.card V : ℝ) ^ 2 ≤ ∑ x ∈ A0, ((A0.filter (G.Adj x)).card : ℝ)
  · exact caseII G φ H hF0 hA0 hA hn1 (by linarith) (by linarith) (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) hcut
  by_cases hB : β * (Fintype.card V : ℝ) ^ 2 ≤
      ∑ x ∈ cn G u0 v0 \ A0, (((cn G u0 v0 \ A0).filter (G.Adj x)).card : ℝ)
  · exact caseII G φ H hF0 (isBalBip_compl G φ hA0) hB hn1 (by linarith) (by linarith)
      (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hcut
  push_neg at hA hB
  exact caseI G φ H hβ hf0 hF0 hA0 hA hB hn1 (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)

end NashWilliams.Frac
