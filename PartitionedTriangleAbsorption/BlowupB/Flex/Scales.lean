/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Cert

@[expose] public section

set_option exponentiation.threshold 512

/-!
# Flexible scales for the component walk certificates

`walk_scales` (PaddedNoCommon) fixes `δ = ω¹²/2⁶³` and `ρ = ω²⁶/2²⁶²`. All twelve scale inequalities
of the component walk only need

* `0 < ω ≤ 1`, `0 < δ, 2⁶³ δ ≤ ω`, `2²⁴ ρ ≤ (ω δ / 2⁴⁸)²` (the token layers run at `λ = ω δ / 2⁴⁸`), and `1 ≤ ρ n` (`0 ≤ n`),

with the same internal-load threshold `Q = δ n / 2²⁵` (`walk_scales_flex`). This frees the absorber
degree `δ` and the reserve degree `ρ` from the supply constant `ω`, which is what the transports
(vertex splitting, component re-use) need: a reserve of degree `2 paddedRho(ω) n` stays admissible
for supply `ω / c` and host size `≤ c n` when `δ = paddedAbsDelta(ω) / c'`.
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

/-- The flexible scale hypotheses. -/
structure FlexScales (ω δ ρ n : ℝ) : Prop where
  ω_pos : 0 < ω
  ω_le : ω ≤ 1
  δ_pos : 0 < δ
  δ_le : 2 ^ 63 * δ ≤ ω
  ρ_sq : 2 ^ 24 * ρ ≤ (ω * δ / 2 ^ 48) ^ 2
  n_nonneg : 0 ≤ n
  ρn : 1 ≤ ρ * n

theorem walk_scales_flex (ω n δ ρ lam Q : ℝ) (h : FlexScales ω δ ρ n)
    (hlam : lam = ω * δ / 2 ^ 40) (hQ : Q = δ * n / 2 ^ 25) :
    0 < lam ∧ lam ≤ 1 / 64 ∧ 0 < ρ ∧ 2 ^ 24 * ρ ≤ lam ^ 2 ∧ 256 ≤ lam * n ∧ 0 < δ ∧ 0 < Q ∧
    3 * (4100 * lam * n ^ 2) / Q + 3 +
      2 * (2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 2) < ω * n ∧
    (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < ω * n / 2 ∧
    (2 ^ 21 : ℝ) ≤ δ * n / 4 ∧
    2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) ≤ δ * n ∧
    (2 ^ 21 : ℝ) * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) ≤ δ * n / 2 ∧
    4 * (2 * ρ + 16 * lam + 1224 * ρ * 2 ^ 21) ≤ δ * ω := by
  obtain ⟨hω, hω1, hδ0, hδ1, hsq, hn0, hn⟩ := h
  have hA0 : 0 < ω ^ 12 := by positivity
  have hA1 : ω ^ 12 ≤ ω := pow_le_of_le_one hω.le hω1 (by norm_num)
  have hδω : 2 ^ 63 * δ ≤ ω := hδ1
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hlamδ : 2 ^ 40 * lam ≤ δ := by rw [hlam]; nlinarith
  have hlam_small : 2 ^ 103 * lam ≤ 1 := by nlinarith
  have hρ0 : 0 < ρ := by
    by_contra hc
    have : ρ ≤ 0 := le_of_not_gt hc
    nlinarith
  have hlamsq : 2 ^ 24 * ρ ≤ lam ^ 2 := by
    rw [hlam]
    have h0 : (0 : ℝ) ≤ ω * δ := by positivity
    have : (ω * δ / 2 ^ 48) ^ 2 ≤ (ω * δ / 2 ^ 40) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      exact div_le_div_of_nonneg_left h0 (by positivity) (by norm_num)
    nlinarith
  have hρlam : 2 ^ 127 * ρ ≤ lam := by nlinarith
  have hn0' : 0 < n := by
    by_contra hc
    have : n ≤ 0 := le_of_not_gt hc
    nlinarith
  have hρn : 2 ^ 127 ≤ lam * n := by nlinarith
  have hlamn : 2 ^ 40 * (lam * n) ≤ δ * n := by nlinarith
  have hδn : 2 ^ 63 * (δ * n) ≤ ω * n := by nlinarith
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hdiv : 3 * (4100 * lam * n ^ 2) / Q = 12300 / 2 ^ 15 * ω * n := by
    rw [hQ, hlam]; field_simp; ring
  refine ⟨hlam0, ?_, hρ0, hlamsq, by nlinarith, hδ0, hQ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · rw [hdiv, hQ]; nlinarith
  · nlinarith
  · nlinarith
  · rw [hQ]; nlinarith
  · rw [hQ]; nlinarith
  · nlinarith

/-- The padded scales are flexible scales. -/
theorem flexScales_padded (ω n : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1) (hn0 : 0 ≤ n)
    (hn : 1 ≤ PaddedF12.paddedRho ω * n) :
    FlexScales ω (PaddedF12.paddedAbsDelta ω) (PaddedF12.paddedRho ω) n := by
  have hδ : PaddedF12.paddedAbsDelta ω = ω ^ 12 / 2 ^ 63 := by
    unfold PaddedF12.paddedAbsDelta PaddedF12.paddedKappa; ring
  refine ⟨hω, hω1, by rw [hδ]; positivity, ?_, ?_, hn0, hn⟩
  · rw [hδ]
    have hA1 : ω ^ 12 ≤ ω := pow_le_of_le_one hω.le hω1 (by norm_num)
    have : (2 : ℝ) ^ 63 * (ω ^ 12 / 2 ^ 63) = ω ^ 12 := by field_simp
    linarith
  rw [hδ]
  unfold PaddedF12.paddedRho
  have : (ω * (ω ^ 12 / 2 ^ 63) / 2 ^ 48) ^ 2 = ω ^ 26 / 2 ^ 222 := by ring
  rw [this]
  have : (0 : ℝ) ≤ ω ^ 26 := by positivity
  rw [show (2 : ℝ) ^ 24 * (ω ^ 26 / 2 ^ 262) = ω ^ 26 / 2 ^ 238 by ring]
  exact div_le_div_of_nonneg_left this (by positivity) (by norm_num)

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.walk_scales_flex
#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.flexScales_padded
