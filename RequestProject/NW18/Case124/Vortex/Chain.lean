/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.Vortex.Invariant

/-!
# The whole 12.4 vortex chain with a uniform error schedule

* `sfv m = m^{-1/4}` is the level tolerance; `step_conds` (proved) shows that every numerical
  condition of `inv_step` holds for all levels of size `≥ M₀(k, q)`.
* `exists_chain` (proved, strong induction on `|W|`): from a level `W` with invariant error
  `K · |W|^{-1/4}` (`K = 2D`, `D = 4k/q + 4`) there is a nested chain
  `W = W₀ ⊇ W₁ ⊇ … ⊇ W_L` with `7q/8 |W_i| ≤ |W_{i+1}| ≤ 9q/8 |W_i|`, all nonterminal levels of
  size `≥ M`, `|W_L| < M`, and EVERY level satisfying the invariant with error
  `K · |W_i|^{-1/4}`.  Since `q ≤ 1/32`, a child has at most `1/16` of the parent's size, so
  `|W_{i+1}|^{-1/4} ≥ 2 |W_i|^{-1/4}` and the potential pays for the step cost `D |W_i|^{-1/4}`:
  the errors never accumulate beyond `K · |W_i|^{-1/4}`.
-/

namespace NashWilliams18.Vortex124

open Finset Filter
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The level tolerance `m^{-1/4}`. -/
noncomputable def sfv (m : ℕ) : ℝ := 1 / Real.sqrt (Real.sqrt m)

lemma sfv_pos {m : ℕ} (hm : 0 < m) : 0 < sfv m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold sfv; positivity

lemma sqrt_sqrt_pow4 (m : ℕ) : Real.sqrt (Real.sqrt m) ^ 4 = m := by
  rw [show (4:ℕ) = 2 * 2 by rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
    Real.sq_sqrt (Nat.cast_nonneg _)]

lemma sfv_sq_mul (m : ℕ) : sfv m ^ 2 * m = Real.sqrt m := by
  unfold sfv
  rw [div_pow, one_pow, Real.sq_sqrt (Real.sqrt_nonneg _), one_div_mul_eq_div, Real.div_sqrt]

/-- Shrinking by a factor `16` doubles the tolerance. -/
lemma sfv_shrink {m u : ℕ} (hu : 0 < u) (hum : (u : ℝ) ≤ m / 16) : 2 * sfv m ≤ sfv u := by
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hyu : 0 < Real.sqrt (Real.sqrt u) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hu')
  have hm' : (0 : ℝ) < m := by linarith
  have hym : 0 < Real.sqrt (Real.sqrt m) := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hm')
  have h4 : Real.sqrt (Real.sqrt u) ^ 4 ≤ (Real.sqrt (Real.sqrt m) / 2) ^ 4 := by
    rw [sqrt_sqrt_pow4, div_pow, sqrt_sqrt_pow4]; norm_num; linarith
  have h : Real.sqrt (Real.sqrt u) ≤ Real.sqrt (Real.sqrt m) / 2 :=
    (pow_le_pow_iff_left₀ hyu.le (by positivity) (by norm_num)).mp h4
  unfold sfv
  rw [mul_one_div, div_le_div_iff₀ hym hyu]
  linarith

lemma tendsto_sqrt_nat : Tendsto (fun m : ℕ => Real.sqrt m) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_sfv : Tendsto sfv atTop (nhds 0) := by
  have h := (Real.tendsto_sqrt_atTop.comp tendsto_sqrt_nat)
  have := h.inv_tendsto_atTop
  refine this.congr' (Eventually.of_forall fun m => ?_)
  simp [sfv, Function.comp]

lemma ev_exp_small :
    ∀ᶠ m : ℕ in atTop, ((m : ℝ) + 2) * (2 * Real.exp (-2 * Real.sqrt m)) < 1 / 2 := by
  have hy : Tendsto (fun y : ℝ => (y ^ 2 + 2) * (2 * Real.exp (-2 * y))) atTop (nhds 0) := by
    have h1 : Tendsto (fun y : ℝ => y ^ 2 * Real.exp (-y)) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have h2 : Tendsto (fun y : ℝ => Real.exp (-y)) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have h3 : Tendsto (fun y : ℝ => (y ^ 2 * Real.exp (-y) + 2 * Real.exp (-y)) *
        (2 * Real.exp (-y))) atTop (nhds 0) := by
      have := ((h1.add (h2.const_mul 2)).mul (h2.const_mul 2))
      simpa using this
    refine h3.congr' ?_
    filter_upwards with y
    have : Real.exp (-2 * y) = Real.exp (-y) * Real.exp (-y) := by rw [← Real.exp_add]; ring_nf
    rw [this]; ring
  have := (hy.comp tendsto_sqrt_nat).eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))
  filter_upwards [this] with m hm
  simp only [Function.comp] at hm
  rwa [Real.sq_sqrt (Nat.cast_nonneg m)] at hm

lemma fail_bound_of {k : ℕ} (hk : 1 ≤ k) {q : ℝ} (hq : 0 < q) {m : ℕ} (h5 : 0 < m)
    (h3 : 2 * (k : ℝ) ^ 2 / (q ^ k) ^ 2 < Real.sqrt m)
    (h4 : ((m : ℝ) + 2) * (2 * Real.exp (-2 * Real.sqrt m)) < 1 / 2) :
    ((m : ℝ) + 2) * (2 * Real.exp (-2 * (sfv m * m) ^ 2 / m)) +
      (k : ℝ) ^ 2 * (m : ℝ) ^ (2 * k - 1) / (sfv m * q ^ k * (m : ℝ) ^ k) ^ 2 < 1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast h5
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have hs0 := sfv_pos h5
  have hA : -2 * (sfv m * m) ^ 2 / m = -2 * Real.sqrt m := by
    rw [← sfv_sq_mul m]; field_simp
  have hm2 : ((m : ℝ) ^ k) ^ 2 = (m : ℝ) ^ (2 * k - 1) * m := by
    rw [← pow_mul, ← pow_succ]; congr 1; omega
  have hB : (k : ℝ) ^ 2 * (m : ℝ) ^ (2 * k - 1) / (sfv m * q ^ k * (m : ℝ) ^ k) ^ 2 =
      (k : ℝ) ^ 2 / ((q ^ k) ^ 2 * Real.sqrt m) := by
    have : (sfv m * q ^ k * (m : ℝ) ^ k) ^ 2 =
        (q ^ k) ^ 2 * (sfv m ^ 2 * m) * (m : ℝ) ^ (2 * k - 1) := by
      rw [mul_pow, mul_pow, hm2]; ring
    rw [this, sfv_sq_mul m]
    have : 0 < (m : ℝ) ^ (2 * k - 1) := by positivity
    have : 0 < q ^ k := by positivity
    field_simp
  rw [hA, hB]
  have h3' : (k : ℝ) ^ 2 / ((q ^ k) ^ 2 * Real.sqrt m) < 1 / 2 := by
    have : 0 < q ^ k := by positivity
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at h3
    nlinarith
  linarith

/-- **All numerical conditions of one step hold on large levels.** -/
theorem step_conds (k : ℕ) (hk : 1 ≤ k) (q : ℝ) (hq : 0 < q) :
    ∃ M₀ : ℕ, ∀ m : ℕ, M₀ ≤ m → 0 < m ∧ 0 < sfv m ∧ sfv m ≤ q / 8 ∧ k * sfv m / q ≤ 1 / 2 ∧
      sfv m ≤ 1 / 2 ∧ (k : ℝ) ^ 2 / (q ^ k * m) ≤ sfv m ∧
      ((m : ℝ) + 2) * (2 * Real.exp (-2 * (sfv m * m) ^ 2 / m)) +
        (k : ℝ) ^ 2 * (m : ℝ) ^ (2 * k - 1) / (sfv m * q ^ k * (m : ℝ) ^ k) ^ 2 < 1 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hqk : 0 < q ^ k := pow_pos hq k
  have e1 := tendsto_sfv.eventually
    (gt_mem_nhds (show (0:ℝ) < min (q / 8) (min (q / (2 * k)) (1 / 2)) by positivity))
  have e2 := (Real.tendsto_sqrt_atTop.comp tendsto_sqrt_nat).eventually_ge_atTop
    (max 1 ((k : ℝ) ^ 2 / q ^ k))
  have e3 := tendsto_sqrt_nat.eventually_gt_atTop (2 * (k : ℝ) ^ 2 / (q ^ k) ^ 2)
  have e4 := ev_exp_small
  have e5 := eventually_gt_atTop (0 : ℕ)
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp (((e1.and e2).and e3).and (e4.and e5))
  refine ⟨M₀, fun m hm => ?_⟩
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩ := hM₀ m hm
  simp only [Function.comp] at h2
  have hm' : (0 : ℝ) < m := by exact_mod_cast h5
  have hsq : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm'
  have hss : 0 < Real.sqrt (Real.sqrt m) := Real.sqrt_pos.mpr hsq
  have hs0 : 0 < sfv m := sfv_pos h5
  have hsa : sfv m < q / 8 := lt_of_lt_of_le h1 (min_le_left _ _)
  have hsb : sfv m < q / (2 * k) :=
    lt_of_lt_of_le h1 ((min_le_right _ _).trans (min_le_left _ _))
  have hsc : sfv m < 1 / 2 := lt_of_lt_of_le h1 ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨h5, hs0, hsa.le, ?_, hsc.le, ?_, fail_bound_of hk hq h5 h3 h4⟩
  · rw [div_le_iff₀ hq]
    rw [lt_div_iff₀ (by positivity)] at hsb
    linarith
  · set y := Real.sqrt (Real.sqrt m)
    have hy1 : 1 ≤ y := le_trans (le_max_left _ _) h2
    have hy2 : (k : ℝ) ^ 2 / q ^ k ≤ y := le_trans (le_max_right _ _) h2
    have hmy : (m : ℝ) = y ^ 4 := (sqrt_sqrt_pow4 m).symm
    unfold sfv
    rw [div_le_div_iff₀ (by positivity) hss, one_mul, hmy]
    rw [div_le_iff₀ hqk] at hy2
    have : y ≤ y ^ 3 := by
      nlinarith [mul_nonneg (mul_nonneg hss.le (sub_nonneg.mpr hy1)) (by linarith : (0:ℝ) ≤ y + 1)]
    nlinarith

omit [Fintype V] [DecidableEq V] in
/-- The invariant is monotone in the error. -/
lemma Inv124.mono (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (f : (Fin k → V) → Prop)
    [DecidablePred f] {a₀ b₀ c₀ ρ₀ : ℝ} {W : Finset V} {e e' : ℝ}
    (h : Inv124 G f a₀ b₀ c₀ ρ₀ W e) (hee : e ≤ e') : Inv124 G f a₀ b₀ c₀ ρ₀ W e' := by
  obtain ⟨h1, h2, h3⟩ := h
  have hW : (0 : ℝ) ≤ W.card := Nat.cast_nonneg _
  refine ⟨fun v hv => (h1 v hv).trans (by nlinarith), ?_, ?_⟩
  · have hsub : hiSet G W (b₀ - e) ⊆ hiSet G W (b₀ - e') := by
      intro v hv
      unfold hiSet at hv ⊢
      rw [mem_filter] at hv ⊢
      exact ⟨hv.1, hv.2.trans (by nlinarith)⟩
    have : ((hiSet G W (b₀ - e)).card : ℝ) ≤ (hiSet G W (b₀ - e')).card := by
      exact_mod_cast card_le_card hsub
    nlinarith
  · have : (0 : ℝ) ≤ (W.card : ℝ) ^ k := by positivity
    nlinarith

/-- Prepend a level to a sequence of levels. -/
def consSeq (W : Finset V) (Ws : ℕ → Finset V) : ℕ → Finset V
  | 0 => W
  | k + 1 => Ws k

/-- **The 12.4 vortex chain** (proved). -/
theorem exists_chain (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 1 ≤ k)
    (f : (Fin k → V) → Prop) [DecidablePred f] {a₀ b₀ c₀ ρ₀ : ℝ}
    (ha₀ : 0 ≤ a₀) (ha₁ : a₀ ≤ 1) (hb₀ : 0 ≤ b₀) (hb₁ : b₀ ≤ 1 / 4) (hc₁ : c₀ ≤ 1)
    (hρ₀ : 0 ≤ ρ₀) {q : ℝ≥0} (hq0 : 0 < (q : ℝ)) (hq1 : (q : ℝ) ≤ 1 / 32)
    (M : ℕ)
    (hM : ∀ m : ℕ, M ≤ m → 0 < m ∧ 0 < sfv m ∧ sfv m ≤ q / 8 ∧ k * sfv m / q ≤ 1 / 2 ∧
      sfv m ≤ 1 / 2 ∧ (k : ℝ) ^ 2 / ((q : ℝ) ^ k * m) ≤ sfv m ∧
      ((m : ℝ) + 2) * (2 * Real.exp (-2 * (sfv m * m) ^ 2 / m)) +
        (k : ℝ) ^ 2 * (m : ℝ) ^ (2 * k - 1) / (sfv m * (q : ℝ) ^ k * (m : ℝ) ^ k) ^ 2 < 1)
    (hKM : 2 * (4 * k / q + 4) * sfv M ≤ 1) :
    ∀ (m : ℕ) (W : Finset V), W.card = m → 0 < m →
      Inv124 G f a₀ b₀ c₀ ρ₀ W (2 * (4 * k / q + 4) * sfv m) →
      ∃ (L : ℕ) (Ws : ℕ → Finset V), Ws 0 = W ∧
        (∀ i < L, Ws (i + 1) ⊆ Ws i ∧ M ≤ (Ws i).card ∧
          7 * q / 8 * ((Ws i).card : ℝ) ≤ (Ws (i + 1)).card ∧
          ((Ws (i + 1)).card : ℝ) ≤ 9 * q / 8 * (Ws i).card) ∧
        (Ws L).card < M ∧ 0 < (Ws L).card ∧
        (∀ i ≤ L, Inv124 G f a₀ b₀ c₀ ρ₀ (Ws i) (2 * (4 * k / q + 4) * sfv (Ws i).card)) ∧
        ∀ i < L, ∀ v ∈ Ws i, (nnb G v (Ws (i + 1)) : ℝ) ≤
          (1 / 4 + a₀ + 2 * (4 * k / q + 4) * sfv (Ws (i + 1)).card) * (Ws (i + 1)).card := by
  set D : ℝ := 4 * k / q + 4 with hD
  have hD0 : 0 < D := by positivity
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro W hWm hm0 hinv
  by_cases hsmall : m < M
  · refine ⟨0, fun _ => W, rfl, fun i hi => absurd hi (Nat.not_lt_zero _), by simpa [hWm] using hsmall,
      by simpa [hWm] using hm0, fun i _ => by simpa [hWm] using hinv,
      fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  push_neg at hsmall
  obtain ⟨-, hs0, hsq, hks, hs2, hkm, hfail⟩ := hM m hsmall
  have hW0 : 0 < W.card := hWm ▸ hm0
  have hsM : sfv m ≤ sfv M := by
    unfold sfv
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (hM M le_rfl).1
    apply one_div_le_one_div_of_le (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hM0))
    exact Real.sqrt_le_sqrt (Real.sqrt_le_sqrt (by exact_mod_cast hsmall))
  have he1 : 2 * D * sfv m ≤ 1 := le_trans (by nlinarith) hKM
  rw [← hWm] at hs0 hsq hks hs2 hkm hfail
  rw [← hWm] at he1 hinv
  obtain ⟨U, hUW, hlo, hhi, hUinv, hpar⟩ := inv_step G hk f ha₀ ha₁ hb₀ hb₁ hc₁ hρ₀ hq0 hq1 W hW0
    (e := 2 * D * sfv W.card) (s := sfv W.card) (by positivity) he1 hs0 hsq hks hs2 hkm hfail
    hinv
  have hmR : (0 : ℝ) < W.card := by exact_mod_cast hW0
  have hU0 : 0 < U.card := by
    have : (0 : ℝ) < U.card := lt_of_lt_of_le (by positivity) hlo
    exact_mod_cast this
  have hUm : U.card < m := by
    have : (U.card : ℝ) < W.card := lt_of_le_of_lt hhi (by nlinarith)
    rw [← hWm]; exact_mod_cast this
  have hshr : 2 * sfv W.card ≤ sfv U.card := sfv_shrink hU0 (by nlinarith)
  have hUinv' : Inv124 G f a₀ b₀ c₀ ρ₀ U (2 * D * sfv U.card) := by
    refine Inv124.mono G f hUinv ?_
    have := sfv_pos hW0
    nlinarith
  obtain ⟨L, Ws, h0, hstep, hlast, hlast0, hall, hpar'⟩ := ih U.card hUm U rfl hU0 hUinv'
  refine ⟨L + 1, consSeq W Ws, rfl, ?_, by simpa [consSeq] using hlast,
    by simpa [consSeq] using hlast0, ?_, ?_⟩
  · intro i hi
    rcases i with _ | i
    · simp only [consSeq, h0]
      exact ⟨hUW, by rw [hWm]; exact hsmall, hlo, hhi⟩
    · exact hstep i (by omega)
  · intro i hi
    rcases i with _ | i
    · simpa [consSeq] using hinv
    · exact hall i (by omega)
  · intro i hi
    rcases i with _ | i
    · intro v hv
      simp only [consSeq, h0] at hv ⊢
      have hU0R : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
      have := sfv_pos hW0
      refine (hpar v hv).trans (mul_le_mul_of_nonneg_right ?_ hU0R)
      nlinarith
    · exact hpar' i (by omega)

end NashWilliams18.Vortex124
