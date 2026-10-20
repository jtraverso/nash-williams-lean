/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.StabPerm

@[expose] public section

/-!
# Numerical stability of the four part value bound

`stab_numeric`: a four part configuration (sorted part sizes `x₀ ≥ x₁ ≥ x₂ ≥ x₃`, thin pair
weights `m`) whose value `∑_{i<j} mᵢⱼ xᵢ xⱼ` is at least `1/4 - ρ²` is either close to a cut
(`NumCut`) or is a nearly matched, balanced configuration with all parts and weights bounded
below (`NumQuad`).
-/

namespace NashWilliams.Frac

open Finset

/-- Close to a cut: a set of parts of total size about `1/2` such that the pairs across are
almost all of weight `1`. -/
def NumCut (x : Fin 4 → ℝ) (m : Fin 4 → Fin 4 → ℝ) (δ : ℝ) : Prop :=
  ∃ I : Finset (Fin 4), |∑ i ∈ I, x i - 1/2| ≤ δ ∧
    ∑ i ∈ I, ∑ j ∈ Iᶜ, (1 - m i j) * x i * x j ≤ δ ^ 2

/-- A nearly matched configuration with parts and weights bounded below. -/
def NumQuad (x : Fin 4 → ℝ) (m : Fin 4 → Fin 4 → ℝ) (κ τ θ : ℝ) : Prop :=
  (∀ i, κ ≤ x i) ∧ (∀ i j, i ≠ j → τ ≤ m i j) ∧
  (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l → |m i j - m k l| ≤ θ) ∧
  (∀ i j k, i ≠ j → i ≠ k → j ≠ k → 2 - θ ≤ m i j + m i k + m j k) ∧
  (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l → m i j ≤ 1 - τ →
    |x i + x j - 1/2| ≤ θ) ∧
  4 - sum6 m 0 1 2 3 ≤ θ ^ 2 / 8

variable {x : Fin 4 → ℝ} {m : Fin 4 → Fin 4 → ℝ}

/-- Shorthand for the value of the sorted configuration. -/
abbrev valS (x : Fin 4 → ℝ) (m : Fin 4 → Fin 4 → ℝ) : ℝ :=
  val4 (x 0) (x 1) (x 2) (x 3) (m 0 1) (m 0 2) (m 0 3) (m 1 2) (m 1 3) (m 2 3)

lemma abs_le_of_sq {y δ : ℝ} (hδ : 0 ≤ δ) (h : y ^ 2 ≤ δ ^ 2) : |y| ≤ δ := by
  have := sq_le_sq.1 h; rwa [abs_of_nonneg hδ] at this

lemma numA (H : Cfg4 x m) (h32 : x 3 ≤ x 2) (h21 : x 2 ≤ x 1) (hA : x 1 + x 2 ≤ x 0)
    {ρ δ : ℝ} (hρ : 0 ≤ ρ) (hval : 1/4 - ρ^2 ≤ valS x m) (h1 : 12 * ρ ≤ δ ^ 2) (h2 : ρ ≤ δ) :
    NumCut x m δ := by
  obtain ⟨b, b1, b2, b3⟩ := regimeA (H.thinK4 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)) (H.x0 3) h32 h21 H.sum hA hρ hval
  refine ⟨{0}, ?_, ?_⟩
  · rw [sum_singleton]; exact b.trans h2
  · have hc : ({0} : Finset (Fin 4))ᶜ = {1, 2, 3} := by decide
    rw [sum_singleton, hc, sum_insert (by decide), sum_insert (by decide), sum_singleton]
    linarith

lemma numBsmall (H : Cfg4 x m) (h32 : x 3 ≤ x 2) (h21 : x 2 ≤ x 1) (h10 : x 1 ≤ x 0)
    (hB : x 0 ≤ x 1 + x 2) {ρ κ δ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1/64) (hκ1 : κ ≤ 1/64)
    (hx3 : x 3 ≤ κ) (hval : 1/4 - ρ^2 ≤ valS x m) (h1 : 5 * ρ + 3 * κ ≤ δ ^ 2) (h2 : ρ ≤ δ) :
    NumCut x m δ := by
  obtain ⟨b, b1, b2, b3, b4⟩ := regimeB_small (H.thinK4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) (H.x0 3) h32 h21 h10 H.sum hB hρ hρ1 hκ1 hx3 hval
  refine ⟨{0, 3}, ?_, ?_⟩
  · rw [sum_pair (by decide)]; exact b.trans h2
  · have hc : ({0, 3} : Finset (Fin 4))ᶜ = {1, 2} := by decide
    rw [hc, sum_pair (by decide), sum_pair (by decide), sum_pair (by decide)]
    rw [H.symm 3 1, H.symm 3 2]
    nlinarith

lemma numSmallPair (H : Cfg4 x m) {s D τ δ : ℝ}
    (hs : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 2 - m i j - m i k - m j k ≤ s)
    (hval : 1/4 - D ≤ valS x m) {i j : Fin 4} (hij : i ≠ j) (hm : m i j ≤ τ) (hδ : 0 ≤ δ)
    (h1 : (s + τ) / 4 ≤ δ ^ 2) (h2 : D + τ/2 + s/4 ≤ δ ^ 2) : NumCut x m δ := by
  obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := exists_other_two hij
  have NM := H.nearMatched hs hij hik hil hjk hjl hkl
  have hv : 1/4 - D ≤ val4 (x i) (x j) (x k) (x l) (m i j) (m i k) (m i l) (m j k) (m j l)
      (m k l) := by rw [val4_perm H.symm hij hik hil hjk hjl hkl]; exact hval
  obtain ⟨c1, c2, c3, c4, c5⟩ := smallpair_cut NM hv hm
  refine ⟨{i, j}, ?_, ?_⟩
  · rw [sum_pair hij]; exact abs_le_of_sq hδ (c5.trans h2)
  · rw [compl_pair hij hik hil hjk hjl hkl, sum_pair hij, sum_pair hkl, sum_pair hkl]
    have xi := H.x0 i; have xj := H.x0 j; have xk := H.x0 k; have xl := H.x0 l
    have hq : (x i + x j) * (x k + x l) ≤ 1/4 :=
      mul_le_quarter (by positivity) (by positivity)
        (by rw [show x i + x j + (x k + x l) = x i + x j + x k + x l by ring,
          sum_x_perm hij hik hil hjk hjl hkl, H.sum])
    have e1 : (1 - m i k) * x i * x k ≤ (s + τ) * (x i * x k) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right c1 (by positivity)
    have e2 : (1 - m i l) * x i * x l ≤ (s + τ) * (x i * x l) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right c2 (by positivity)
    have e3 : (1 - m j k) * x j * x k ≤ (s + τ) * (x j * x k) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right c3 (by positivity)
    have e4 : (1 - m j l) * x j * x l ≤ (s + τ) * (x j * x l) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_right c4 (by positivity)
    have hst : 0 ≤ s + τ := le_trans (by linarith [H.le1 i k]) c1
    have : (s + τ) * ((x i + x j) * (x k + x l)) ≤ (s + τ) * (1/4) :=
      mul_le_mul_of_nonneg_left hq hst
    nlinarith

lemma numQuad (H : Cfg4 x m) {s D κ τ θ : ℝ}
    (hs : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 2 - m i j - m i k - m j k ≤ s)
    (hval : 1/4 - D ≤ valS x m) (hτ : ∀ i j, i ≠ j → τ ≤ m i j) (hκ : ∀ i, κ ≤ x i)
    (hθ : 0 ≤ θ) (hτ0 : 0 < τ) (h1 : s ≤ θ) (h2 : 2 * s ≤ τ) (h3 : 2 * D + 2 * s ≤ θ ^ 2 * τ)
    (h4 : 2 * s ≤ θ ^ 2 / 8) : NumQuad x m κ τ θ := by
  refine ⟨hκ, hτ, ?_, ?_, ?_, ?_⟩
  · intro i j k l hij hik hil hjk hjl hkl
    exact ((H.nearMatched hs hij hik hil hjk hjl hkl).match_err.1).trans h1
  · intro i j k hij hik hjk
    linarith [hs i j k hij hik hjk]
  · intro i j k l hij hik hil hjk hjl hkl hm
    have NM := H.nearMatched hs hij hik hil hjk hjl hkl
    have hv : 1/4 - D ≤ val4 (x i) (x j) (x k) (x l) (m i j) (m i k) (m i l) (m j k) (m j l)
        (m k l) := by rw [val4_perm H.symm hij hik hil hjk hjl hkl]; exact hval
    have hb := matching_balance NM hv hm h2
    refine abs_le_of_sq hθ ?_
    have : (x i + x j - 1/2) ^ 2 * τ ≤ θ ^ 2 * τ := hb.trans h3
    exact le_of_mul_le_mul_right this hτ0
  · have a := hs 0 1 2 (by decide) (by decide) (by decide)
    have b := hs 0 1 3 (by decide) (by decide) (by decide)
    have c := hs 0 2 3 (by decide) (by decide) (by decide)
    have d := hs 1 2 3 (by decide) (by decide) (by decide)
    unfold sum6; linarith

/-- **Numerical stability.** -/
theorem stab_numeric {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1/2) {θ : ℝ} (hθ : 0 < θ) :
    ∃ ρ > 0, ∀ (x : Fin 4 → ℝ) (m : Fin 4 → Fin 4 → ℝ), Cfg4 x m → x 3 ≤ x 2 → x 2 ≤ x 1 →
      x 1 ≤ x 0 → 1/4 - ρ^2 ≤ valS x m → NumCut x m δ ∨ NumQuad x m (δ^2/24) (δ^2/16) θ := by
  set κ : ℝ := δ^2/24 with hκdef
  set τ : ℝ := δ^2/16 with hτdef
  have hκ0 : 0 < κ := by positivity
  have hτ0 : 0 < τ := by positivity
  have hδ2 : δ ^ 2 ≤ δ / 2 := by nlinarith
  set σ0 : ℝ := min θ (min (θ^2/16) (min (τ/2) (min (δ^2) (θ^2*τ/4)))) with hσdef
  have hσ0 : 0 < σ0 := by positivity
  have s1 : σ0 ≤ θ := min_le_left _ _
  have s2 : σ0 ≤ θ^2/16 := (min_le_right _ _).trans (min_le_left _ _)
  have s3 : σ0 ≤ τ/2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have s4 : σ0 ≤ δ^2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have s5 : σ0 ≤ θ^2*τ/4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  set ρ : ℝ := min (δ^2/12) (min (1/64) (min (κ/4) (min (κ^2*σ0/4) (θ^2*τ/4)))) with hρdef
  have hρ0 : 0 < ρ := by positivity
  have r1 : ρ ≤ δ^2/12 := min_le_left _ _
  have r2 : ρ ≤ 1/64 := (min_le_right _ _).trans (min_le_left _ _)
  have r3 : ρ ≤ κ/4 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have r4 : ρ ≤ κ^2*σ0/4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have r5 : ρ ≤ θ^2*τ/4 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hρsq : ρ ^ 2 ≤ ρ := by nlinarith
  refine ⟨ρ, hρ0, fun x m H h32 h21 h10 hval => ?_⟩
  by_cases hA : x 1 + x 2 ≤ x 0
  · exact Or.inl (numA H h32 h21 hA hρ0.le hval (by linarith) (by linarith))
  push_neg at hA
  by_cases hsm : x 3 ≤ κ
  · exact Or.inl (numBsmall H h32 h21 h10 hA.le hρ0.le r2 (by rw [hκdef]; nlinarith) hsm hval
      (by rw [hκdef]; linarith) (by linarith))
  push_neg at hsm
  obtain ⟨-, b1, b2, b3, b4⟩ := regimeB_big (H.thinK4 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)) h32 h21 h10 H.sum hA.le hρ0.le hκ0 r3 hsm.le hval
  have hk2 : 0 < κ ^ 2 := by positivity
  have conv : ∀ t : ℝ, t * κ ^ 2 ≤ 4 * ρ ^ 2 → t ≤ σ0 := fun t ht => by
    have : t * κ ^ 2 ≤ σ0 * κ ^ 2 := by nlinarith
    exact le_of_mul_le_mul_right this hk2
  have hs := H.slack_all (s := σ0) (by linarith [conv _ b1]) (by linarith [conv _ b2])
    (by linarith [conv _ b3]) (by linarith [conv _ b4])
  have hval' : 1/4 - ρ^2 ≤ valS x m := hval
  by_cases hsp : ∃ i j, i ≠ j ∧ m i j < τ
  · obtain ⟨i, j, hij, hm⟩ := hsp
    exact Or.inl (numSmallPair H hs hval' hij hm.le hδ.le (by linarith) (by linarith))
  push_neg at hsp
  refine Or.inr (numQuad H hs hval' (fun i j hij => hsp i j hij) ?_ hθ.le hτ0 s1
    (by linarith) (by linarith) (by linarith))
  intro i; fin_cases i
  · show κ ≤ x 0; linarith
  · show κ ≤ x 1; linarith
  · show κ ≤ x 2; linarith
  · show κ ≤ x 3; linarith

end NashWilliams.Frac
