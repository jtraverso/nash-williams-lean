/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.GlobalMain

@[expose] public section

/-!
# Establishing the `Setting` of the global part of Theorem 10.9

`setting_of` derives all the facts collected in `Setting` from Claims 10.9.1 and 10.9.2, the
cleaning lemma and the bound on `S`, for the parameters `α = r²`, `κ = s = ζ = r`.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- `σ`-extremality is monotone in `σ`. -/
lemma isExtremal_mono {σ σ' : ℝ} (h : σ' ≤ σ) (hG : NashWilliams18.IsExtremal σ' G) :
    NashWilliams18.IsExtremal σ G := by
  obtain ⟨h1, S, h2⟩ := hG
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  refine ⟨?_, S, ?_⟩
  · refine le_trans (by nlinarith) (le_trans h1 ?_)
    exact_mod_cast card_le_card (monotone_filter_right _ fun v _ hv => by nlinarith)
  · exact le_trans (by nlinarith [sq_nonneg (Fintype.card V : ℝ)]) h2

/-- The facts of the global part of Theorem 10.9. -/
theorem setting_of (hφ : GoodWeighting G φ) {ε t γ r F₀ : ℝ}
    (hδ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree)
    (hr0 : 0 < r) (hr1 : r ≤ 1 / 400000) (hε0 : 0 ≤ ε) (hεt : ε ≤ t ^ 2) (hε12 : ε ≤ 1 / 12)
    (ht0 : 0 < t) (ht : t ≤ 1 / 20) (htγ : t ≤ γ) (hγ2 : t + 4 * ε ≤ γ ^ 2)
    (hclean : t ≤ 4 * r ^ 3 - 4 * ε) (hF₀ : 0 < F₀) (hmax : ∀ g ∈ E2 G φ t, negW φ g ≤ F₀)
    (hQ : ((Qp G φ t F₀).card : ℝ) < 32 / 3 * (ε / t) * (Fintype.card V : ℝ) ^ 2)
    (hQa : 32 / 3 * (ε / t) ≤ 1 / 45) (hQb : 32 / 3 * (ε / t) ≤ γ / 100)
    (hQc : 32 / 3 * (ε / t) ≤ r ^ 2)
    (hLS1 : ∀ u v, G.Adj u v → φ s(u, v) < 0 → chNeg G φ u v ≤ γ * (-φ s(u, v)) →
      LocallySmall G φ (4 * γ) u v ∨ IsBip G φ ((r ^ 2) ^ 2 / 2) u v)
    (hLS2 : ∀ u v, G.Adj u v → φ s(u, v) < 0 → chNeg G φ u v ≤ 2 * γ * (-φ s(u, v)) →
      LocallySmall G φ (1 / 200) u v ∨ IsBip G φ (1 / 5) u v) :
    Setting G φ ε t (r ^ 2) r r r r F₀ := by
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hr2 : r ^ 2 ≤ 1 / 100 := by nlinarith
  have hQ1 : ((Qp G φ t F₀).card : ℝ) < (Fintype.card V : ℝ) ^ 2 / 45 := by
    have := mul_le_mul_of_nonneg_right hQa (sq_nonneg (Fintype.card V : ℝ)); linarith
  have hQ2 : ((Qp G φ t F₀).card : ℝ) < γ * (Fintype.card V : ℝ) ^ 2 / 100 := by
    have := mul_le_mul_of_nonneg_right hQb (sq_nonneg (Fintype.card V : ℝ)); linarith
  refine
    { hφ := hφ
      δ := hδ
      F₀pos := hF₀
      max := hmax
      cn_le := fun f hf => claim2_cn G φ hφ hε0 hεt ht0 ht hδ hf
      bip := fun f hf hfH => claim2_bip G φ hφ hε12 ht0 htγ hγ2 (sq_nonneg r) (by linarith) hF₀ hδ
        hmax hQ1 hQ2 hLS1 hLS2 hf hfH
      clean := ?_
      S_le := ?_
      hr := hr0
      hαr := by nlinarith
      hα0 := sq_nonneg r
      hα := hr2
      hε0 := hε0
      ht0 := ht0.le
      ht := ht
      hκ0 := hr0.le
      hκ := by linarith
      hs := hr0.le }
  · intro f hf
    by_contra hc
    push_neg at hc
    obtain ⟨u, v⟩ := f
    have hf' := hf
    simp only [E2, mem_sdiff, mem_union, not_or] at hf'
    obtain ⟨hfN, hf0, -⟩ := hf'
    obtain ⟨huv, hneg⟩ := (mem_negPairs G φ).1 hfN
    simp (config := { failIfUnchanged := false }) only at huv hneg hc
    have hch : chNeg G φ u v < t * (-φ s(u, v)) := by
      simp only [E0, mem_filter, not_and, not_le] at hf0
      exact hf0 hfN
    unfold ucSet at hc
    have := chNeg_cleaning G φ hφ hr0.le (by linarith) hδ huv hneg hc
    have : (-φ s(u, v)) * t ≤ (-φ s(u, v)) * (4 * r ^ 3 - 4 * ε) :=
      mul_le_mul_of_nonneg_left hclean (by linarith)
    linarith
  · have h1 := card_SS_mul_le G φ t F₀ r
    rcases hn0.eq_or_lt with h0 | hpos
    · have : (SS G φ t F₀ r).card = 0 := by
        have := card_le_univ (SS G φ t F₀ r)
        have h0' : Fintype.card V = 0 := by exact_mod_cast h0.symm
        omega
      rw [this, ← h0]; simp
    · have h2 : ((SS G φ t F₀ r).card : ℝ) * (r * Fintype.card V) <
          (r * Fintype.card V) * (r * Fintype.card V) := by
        have := mul_le_mul_of_nonneg_right hQc (sq_nonneg (Fintype.card V : ℝ))
        nlinarith
      have := lt_of_mul_lt_mul_right h2 (by positivity)
      linarith

end NashWilliams.Frac
