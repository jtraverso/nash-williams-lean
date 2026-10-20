/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.Assemble
public import RequestProject.FracStab.Dual
public import RequestProject.NW18.Defs

@[expose] public section

/-!
# Theorem 1.6 (fractional stability) from Theorem 10.9

`rules_nonneg` is the core of Theorem 10.9 of the paper: if `G` has `δ(G) ≥ (3/4 - ε) n` and is
not `σ`-extremal, then after the Demand Proportional rule and the two additional rules every
negative pair has nonnegative charge.  Since all three rules preserve the total charge and
positive edges keep a nonnegative charge, every good weighting has nonnegative value
(`frac_stability`), and Theorem 1.6 follows from Farkas' lemma (`theorem_1_6_proof`).
-/

namespace NashWilliams.Frac

open Finset

lemma aux_bip {γ r : ℝ} (h : γ ≤ r ^ 4 / 600) : 36 * (4 * γ) + (r ^ 2) ^ 2 / 4 ≤ (r ^ 2) ^ 2 / 2 := by
  have e : (r ^ 2) ^ 2 = r ^ 4 := by ring
  rw [e]
  nlinarith [pow_two_nonneg (r ^ 2)]

set_option maxHeartbeats 1000000 in
/-- **Theorem 10.9 (core).** For every `σ > 0` there are `ε > 0`, a threshold `t` and `n₀` such
that, if `G` has `n ≥ n₀` vertices, `δ(G) ≥ (3/4 - ε) n` and is not `σ`-extremal, then every
negative pair has nonnegative charge after the additional rules. -/
theorem rules_nonneg (σ : ℝ) (hσ : 0 < σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ t : ℝ, ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Sym2 V → ℝ),
      n₀ ≤ Fintype.card V → (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      GoodWeighting G φ → ¬ NashWilliams18.IsExtremal σ G →
      ∀ g ∈ negPairs G φ, 0 ≤ ch2 G φ t g := by
  set p := min σ (1 / 100) with hp
  have hp0 : 0 < p := lt_min hσ (by norm_num)
  have hpσ : p ≤ σ := min_le_left _ _
  have hp1 : p ≤ 1 / 100 := min_le_right _ _
  set r := p / 4000 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 400000 := by rw [hr]; linarith
  obtain ⟨γ₁, hγ₁, hLS₁⟩ := local_structure ((r ^ 2) ^ 2 / 4) (by positivity)
  obtain ⟨γ₂, hγ₂, hLS₂⟩ := local_structure (1 / 50) (by norm_num)
  set γ := min (min γ₁ (γ₂ / 2)) (r ^ 4 / 600) with hγ
  have hγ0 : 0 < γ := lt_min (lt_min hγ₁ (by linarith)) (by positivity)
  have hγa : γ ≤ γ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hγb : γ ≤ γ₂ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hγc : γ ≤ r ^ 4 / 600 := min_le_right _ _
  have hr4 : r ^ 4 ≤ 1 := by
    have : r ≤ 1 := by linarith
    calc r ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ hr0.le this 4
      _ = 1 := by norm_num
  have hγ1 : γ ≤ 1 / 600 := by linarith
  obtain ⟨n₁, hn₁⟩ := hLS₁ γ hγ0 hγa
  obtain ⟨n₂, hn₂⟩ := hLS₂ (2 * γ) (by positivity) (by linarith)
  set t := min (γ ^ 2 / 2) (2 * r ^ 3) with ht
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have hta : t ≤ γ ^ 2 / 2 := min_le_left _ _
  have htb : t ≤ 2 * r ^ 3 := min_le_right _ _
  have hr3 : r ^ 3 ≤ r := by
    have h1 : r ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have htr : t ≤ r := by
    have : 2 * r ^ 3 ≤ r := by
      have : r ^ 2 ≤ 1 / 2 := by nlinarith
      nlinarith
    linarith
  have ht1 : t ≤ 1 / 20 := by linarith
  have hγγ : γ ^ 2 ≤ γ := by nlinarith
  have htγ : t ≤ γ := by linarith
  set ε := t ^ 2 * r ^ 2 * γ / 1000 with hε
  have hε0 : 0 < ε := by positivity
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hεt2 : ε ≤ t ^ 2 / 1000 := by
    rw [hε]
    have : r ^ 2 * γ ≤ 1 := by nlinarith
    have : t ^ 2 * (r ^ 2 * γ) ≤ t ^ 2 * 1 := mul_le_mul_of_nonneg_left this (sq_nonneg t)
    nlinarith
  have htt : t ^ 2 ≤ t := by nlinarith
  have hεt' : ε / t = t * r ^ 2 * γ / 1000 := by rw [hε]; field_simp
  have hεγ : ε ≤ γ ^ 2 := by linarith
  clear_value ε t γ r p
  refine ⟨ε, hε0, t, max (max n₁ n₂) ⌈1 / r⌉₊, ?_⟩
  intro V _ _ G _ φ hn hδ hφ hext g hg
  have hn₁' : n₁ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₂' : n₂ ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ r * Fintype.card V := by
    have h1 : (⌈1 / r⌉₊ : ℝ) ≤ Fintype.card V := by
      exact_mod_cast le_trans (le_max_right _ _) hn
    have h2 : 1 / r ≤ (⌈1 / r⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : 1 / r ≤ (Fintype.card V : ℝ) := h2.trans h1
    rw [div_le_iff₀ hr0] at h3
    linarith only [h3]
  clear hn
  by_contra hneg
  push_neg at hneg
  have hg_neg := hg
  have hg_bad := hneg
  have hgE : g ∉ E0 G φ t ∪ E1 G φ t := fun h => by
    exact absurd (ch2_nonneg_of_mem G φ ht0.le (mem_union.1 h)) (not_le.2 hg_bad)
  have hgE2 : g ∈ E2 G φ t := mem_sdiff.2 ⟨hg_neg, hgE⟩
  obtain ⟨f0, hf0, hmax⟩ := exists_max_image (E2 G φ t) (negW φ) ⟨g, hgE2⟩
  have hF₀ : 0 < negW φ f0 := by
    obtain ⟨-, h⟩ := (mem_negPairs G φ).1 (E2_subset G φ t hf0); unfold negW; exact neg_pos.2 h
  have hQ := card_Qp_lt G φ hφ hε0.le ht0 hF₀ hδ hg_neg hgE (hmax g hgE2) hg_bad
  have hLS1 : ∀ u v, G.Adj u v → φ s(u, v) < 0 → chNeg G φ u v ≤ γ * (-φ s(u, v)) →
      LocallySmall G φ (4 * γ) u v ∨ IsBip G φ ((r ^ 2) ^ 2 / 2) u v := by
    intro u v huv hneg' hch
    rcases hn₁ ε hε0.le hεγ (4 * γ) (by positivity) (by linarith only [hγ1]) V G φ hn₁' hφ hδ u v
      huv hneg' hch with h | h
    · exact Or.inl h
    · exact Or.inr (isBip_mono G φ (aux_bip hγc) hneg' h)
  have hLS2 : ∀ u v, G.Adj u v → φ s(u, v) < 0 → chNeg G φ u v ≤ 2 * γ * (-φ s(u, v)) →
      LocallySmall G φ (1 / 200) u v ∨ IsBip G φ (1 / 5) u v := by
    intro u v huv hneg' hch
    rcases hn₂ ε hε0.le (by linarith only [hεγ, sq_nonneg γ]) (1 / 200) (by norm_num) (by norm_num)
      V G φ hn₂' hφ hδ u v huv hneg' hch with h | h
    · exact Or.inl h
    · exact Or.inr (isBip_mono G φ (by norm_num) hneg' h)
  have hQe : 32 / 3 * (ε / t) = 32 / 3 * (t * r ^ 2 * γ / 1000) := by rw [hεt']
  have htr2 : t * r ^ 2 ≤ 1 / 20 := by
    have : t * r ^ 2 ≤ 1 / 20 * 1 := mul_le_mul ht1 hr2 (sq_nonneg r) (by norm_num)
    linarith only [this]
  have htrγ : t * r ^ 2 * γ ≤ 1 / 600 := by
    have h2 : t * r ^ 2 * γ ≤ 1 / 20 * γ := mul_le_mul_of_nonneg_right htr2 hγ0.le
    linarith only [h2, hγ1, hγ0]
  have htγ1 : t * γ ≤ 1 := by
    have : t * γ ≤ 1 * 1 := mul_le_mul (by linarith only [ht1]) (by linarith only [hγ1]) hγ0.le
      zero_le_one
    linarith only [this]
  have hQa : 32 / 3 * (ε / t) ≤ 1 / 45 := by rw [hQe]; linarith only [htrγ]
  have hQb : 32 / 3 * (ε / t) ≤ γ / 100 := by
    rw [hQe]
    have h2 : t * r ^ 2 * γ ≤ 1 / 20 * γ := mul_le_mul_of_nonneg_right htr2 hγ0.le
    linarith only [h2, hγ0]
  have hQc : 32 / 3 * (ε / t) ≤ r ^ 2 := by
    rw [hQe]
    have e : t * r ^ 2 * γ = r ^ 2 * (t * γ) := by ring
    have h2 : r ^ 2 * (t * γ) ≤ r ^ 2 * 1 := mul_le_mul_of_nonneg_left htγ1 (sq_nonneg r)
    linarith only [e, h2, sq_nonneg r]
  have hr3pos : 0 < r ^ 3 := pow_pos hr0 3
  have H := setting_of G φ hφ hδ hr0 hr1 hε0.le (by linarith only [hεt2, sq_nonneg t])
    (by linarith only [hεt2, htt, ht1]) ht0 ht1 htγ
    (by linarith only [hta, hεt2, htt, htγ, hγγ, sq_nonneg γ])
    (by linarith only [htb, hεt2, htt, hr3pos]) hF₀ hmax hQ hQa hQb hQc hLS1 hLS2
  have hext' := global_main G φ H (u0 := f0.1) (v0 := f0.2) hf0 le_rfl hn1 (σ := p)
    (le_of_eq (by rw [hr]; ring)) (by linarith only [sq_nonneg r]) (by linarith only [hεt2, htt, htr, hr0])
    htr le_rfl le_rfl le_rfl le_rfl hr1
  exact hext (isExtremal_mono G hpσ hext')

/-- **Fractional stability, dual form.** Every good weighting of a graph with
`δ(G) ≥ (3/4 - ε) n` which is not `σ`-extremal has nonnegative value. -/
theorem frac_stability (σ : ℝ) (hσ : 0 < σ) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ¬ NashWilliams18.IsExtremal σ G → ∀ φ : Sym2 V → ℝ, GoodWeighting G φ →
      0 ≤ ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0) := by
  obtain ⟨ε, hε, t, n₀, h⟩ := rules_nonneg σ hσ
  refine ⟨ε, hε, n₀, fun V _ _ G _ hn hδ hext φ hφ => ?_⟩
  have h2 := h V G φ hn hδ hφ hext
  have hs := sum_ch2 G φ t
  have hle := sum_chNeg_le G φ hφ
  have h0 : 0 ≤ ∑ g ∈ negPairs G φ, ch2 G φ t g := sum_nonneg h2
  linarith

/-- **Theorem 1.6** (Fractional stability), in the form of `NashWilliams18.theorem_1_6`. -/
theorem theorem_1_6_proof :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W] (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
        n₀ ≤ Fintype.card W → (3 / 4 - ε) * (Fintype.card W : ℝ) ≤ (Gr.minDegree : ℝ) →
        ¬ NashWilliams.HasFractionalTriangleDecomposition Gr →
        NashWilliams18.IsExtremal σ Gr := by
  refine ⟨1, one_pos, fun σ hσ _ => ?_⟩
  obtain ⟨ε, hε, n₀, h⟩ := frac_stability σ hσ
  refine ⟨ε, hε, n₀, fun W _ _ Gr _ hn hδ hno => ?_⟩
  by_contra hext
  exact hno (hasFrac_of_good Gr fun φ hφ => h W Gr hn hδ hext φ hφ)

end NashWilliams.Frac
