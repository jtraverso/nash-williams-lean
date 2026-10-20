/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BernoulliExposure
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-! # Rare-coordinate bounded differences on the finite Bernoulli cube

Everything is stated for the accepted recursive product expectation
`BernoulliExposure.cubeMean`. Probabilities are `cubeMean` of event indicators
(`cubeProb`); `cubeMean_eq_sum_prod` checks that this is the usual finite
product-measure sum. No martingale, MGF or tail estimate is assumed: the
one-coin exponential bound is derived from the exponential series, iterated
along the recursive definition of `cubeMean`, and combined with an indicator
(Markov) comparison.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BernoulliConcentration

open BernoulliExposure Finset

/-! ## Elementary facts -/

open Nat in
/-- Exponential series bound from the second term onwards:
`e^x ≤ 1 + x + x²/(2(1-r))` whenever `|x| ≤ r < 1`. -/
theorem exp_le_one_add_add_sq_div (x r : ℝ) (hx : |x| ≤ r) (hr : r < 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / (2 * (1 - r)) := by
  have hE : HasSum (fun n : ℕ => x ^ n / (n ! : ℝ)) (Real.exp x) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp x
  set a := |x| with ha
  have ha0 : 0 ≤ a := abs_nonneg x
  have ha1 : a < 1 := lt_of_le_of_lt hx hr
  have hG : HasSum (fun n : ℕ => a ^ n) (1 - a)⁻¹ := hasSum_geometric_of_lt_one ha0 ha1
  have hG2 : HasSum (fun n : ℕ => a ^ (n + 2) / 2) (a ^ 2 * (1 - a)⁻¹ / 2) := by
    have := (hG.mul_left (a ^ 2)).div_const 2
    simpa [pow_add, mul_comm] using this
  have hE2 : HasSum (fun n : ℕ => x ^ (n + 2) / ((n + 2) ! : ℝ))
      (Real.exp x - ∑ i ∈ Finset.range 2, x ^ i / (i ! : ℝ)) :=
    (hasSum_nat_add_iff' 2).mpr hE
  have hle := hasSum_le (fun n => ?_) hE2 hG2
  · have hsum : (∑ i ∈ Finset.range 2, x ^ i / (i ! : ℝ)) = 1 + x := by
      norm_num [Finset.sum_range_succ]
    rw [hsum] at hle
    have h1 : a ^ 2 = x ^ 2 := by rw [ha, sq_abs]
    have h2 : a ^ 2 * (1 - a)⁻¹ / 2 ≤ x ^ 2 / (2 * (1 - r)) := by
      rw [h1, div_le_div_iff₀ (by norm_num) (by linarith), ← div_eq_mul_inv]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg x]
    linarith
  · have hf : (2 : ℝ) ≤ ((n + 2) ! : ℝ) := by
      have : 2 ≤ (n + 2) ! := by
        calc 2 = (2 : ℕ) ! := rfl
          _ ≤ (n + 2) ! := Nat.factorial_le (by omega)
      exact_mod_cast this
    have hxa : x ^ (n + 2) ≤ a ^ (n + 2) := by
      rw [ha, ← abs_pow]; exact le_abs_self _
    calc x ^ (n + 2) / ((n + 2) ! : ℝ) ≤ a ^ (n + 2) / ((n + 2) ! : ℝ) := by
          gcongr
      _ ≤ a ^ (n + 2) / 2 := by
          apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hf

theorem coinMean_mono (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (f g : Bool → ℝ)
    (hfg : ∀ b, f b ≤ g b) : coinMean q f ≤ coinMean q g := by
  unfold coinMean
  have := hfg false; have := hfg true
  have h1 : 0 ≤ 1 - q := by linarith
  nlinarith

theorem cubeMean_const_mul {n : ℕ} (q : Fin n → ℝ) (a : ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeMean q (fun ω => a * f ω) = a * cubeMean q f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cubeMean, coinMean, ih]
    ring

theorem cubeMean_neg {n : ℕ} (q : Fin n → ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeMean q (fun ω => -f ω) = -cubeMean q f := by
  have := cubeMean_const_mul q (-1) f
  simpa using this

/-! ## The finite product expectation is the product-measure sum -/

/-- The product weight of an assignment. -/
def cubeWeight {n : ℕ} (q : Fin n → ℝ) (ω : Fin n → Bool) : ℝ :=
  ∏ i, if ω i then q i else 1 - q i

/-- Sanity check: the recursive expectation is the usual finite sum against the
product of the Bernoulli marginals (unequal probabilities, including `0, 1`). -/
theorem cubeMean_eq_sum_prod {n : ℕ} (q : Fin n → ℝ) (f : (Fin n → Bool) → ℝ) :
    cubeMean q f = ∑ ω, cubeWeight q ω * f ω := by
  induction n with
  | zero =>
    simp [cubeMean, cubeWeight, Unique.eq_default (Fin.elim0 : Fin 0 → Bool)]
  | succ n ih =>
    rw [cubeMean, coinMean, ih, ih]
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp [Fin.consEquiv, cubeWeight, Fin.prod_univ_succ, Finset.mul_sum, mul_assoc]
    ring

/-- Probability of an event: the product expectation of its indicator. -/
noncomputable def cubeProb {n : ℕ} (q : Fin n → ℝ) (S : (Fin n → Bool) → Prop) : ℝ :=
  cubeMean q (fun ω => by classical exact if S ω then 1 else 0)

/-! ## The one-coin exponential bound -/

/-- Conditional exponential bound for one centered increment `(X-q)a`, `|a| ≤ c ≤ L`. -/
theorem coin_exp_bound (q c L lam : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hlam : 0 ≤ lam) (hlamL : lam * L < 1) (g : Bool → ℝ)
    (hgap : |g true - g false| ≤ c) (hcL : c ≤ L) :
    coinMean q (fun b => Real.exp (lam * coinIncrement q g b)) ≤
      Real.exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L))) := by
  set a := g true - g false
  have hK : 0 < 1 - lam * L := by linarith
  have habs : ∀ b, |lam * coinIncrement q g b| ≤ lam * L := by
    intro b
    have hz : |coinIncrement q g b| ≤ L := by
      cases b
      · rw [increment_false, abs_mul, abs_neg, abs_of_nonneg hq0]
        calc q * |a| ≤ 1 * |a| := by gcongr
          _ ≤ L := by linarith
      · rw [increment_true, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - q)]
        calc (1 - q) * |a| ≤ 1 * |a| := by gcongr; linarith
          _ ≤ L := by linarith
    rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left hz hlam
  have hpt := fun b => exp_le_one_add_add_sq_div _ _ (habs b) hlamL
  calc coinMean q (fun b => Real.exp (lam * coinIncrement q g b))
      ≤ coinMean q (fun b => 1 + lam * coinIncrement q g b +
          (lam * coinIncrement q g b) ^ 2 / (2 * (1 - lam * L))) :=
        coinMean_mono q hq0 hq1 _ _ hpt
    _ = 1 + lam * coinMean q (coinIncrement q g) + lam ^ 2 / (2 * (1 - lam * L)) *
          coinMean q (fun b => coinIncrement q g b ^ 2) := by
        unfold coinMean; ring
    _ ≤ 1 + lam * 0 + lam ^ 2 / (2 * (1 - lam * L)) * (q * c ^ 2) := by
        rw [increment_centered]
        gcongr
        exact increment_variance_le q c g hq0 hq1 hgap
    _ = 1 + lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L)) := by ring
    _ ≤ _ := by
        have := Real.add_one_le_exp (lam ^ 2 * (q * c ^ 2) / (2 * (1 - lam * L)))
        linarith

/-! ## Iterated exponential moment bound -/

/-- The bounded-differences hypothesis: flipping coordinate `i` changes `f` by at most `c i`. -/
def CoordBounded {n : ℕ} (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) : Prop :=
  ∀ i ω, |f (Function.update ω i true) - f (Function.update ω i false)| ≤ c i

theorem CoordBounded.tail {n : ℕ} {f : (Fin (n + 1) → Bool) → ℝ} {c : Fin (n + 1) → ℝ}
    (h : CoordBounded f c) (b : Bool) :
    CoordBounded (fun ω => f (Fin.cons b ω)) (fun i => c i.succ) := by
  intro i ω
  have := h i.succ (Fin.cons b ω)
  simpa [← Fin.cons_update] using this

theorem CoordBounded.head {n : ℕ} {f : (Fin (n + 1) → Bool) → ℝ} {c : Fin (n + 1) → ℝ}
    (h : CoordBounded f c) (ω : Fin n → Bool) :
    |f (Fin.cons true ω) - f (Fin.cons false ω)| ≤ c 0 := by
  have := h 0 (Fin.cons true ω)
  simpa [Fin.update_cons_zero] using this

theorem CoordBounded.neg {n : ℕ} {f : (Fin n → Bool) → ℝ} {c : Fin n → ℝ}
    (h : CoordBounded f c) : CoordBounded (fun ω => -f ω) c := by
  intro i ω
  have := h i ω
  rw [← abs_neg]; convert this using 2; ring

/-- Exponential moment bound for the centered function, for `0 ≤ λ`, `λL < 1`. -/
theorem cube_mgf_le {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) (L lam : ℝ)
    (hcL : ∀ i, c i ≤ L) (hf : CoordBounded f c)
    (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    cubeMean q (fun ω => Real.exp (lam * (f ω - cubeMean q f))) ≤
      Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
  induction n with
  | zero =>
    simp [cubeMean]
  | succ n ih =>
    set q' : Fin n → ℝ := fun i => q i.succ
    set M : Bool → ℝ := fun b => cubeMean q' (fun ω => f (Fin.cons b ω)) with hM
    have hmean : cubeMean q f = coinMean (q 0) M := rfl
    set K := 2 * (1 - lam * L)
    set V' := ∑ i : Fin n, q' i * (c i.succ) ^ 2
    have hstep : ∀ b, cubeMean q' (fun ω => Real.exp (lam * (f (Fin.cons b ω) -
        cubeMean q f))) ≤ Real.exp (lam * coinIncrement (q 0) M b) *
          Real.exp (lam ^ 2 * V' / K) := by
      intro b
      have hsplit : (fun ω => Real.exp (lam * (f (Fin.cons b ω) - cubeMean q f))) =
          fun ω => Real.exp (lam * coinIncrement (q 0) M b) *
            Real.exp (lam * (f (Fin.cons b ω) - M b)) := by
        funext ω
        rw [← Real.exp_add, hmean, coinIncrement]
        ring_nf
      rw [hsplit, cubeMean_const_mul]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact ih q' (fun i => hq i.succ) _ (fun i => c i.succ) (fun i => hcL i.succ)
        (hf.tail b)
    have hgap : |M true - M false| ≤ c 0 :=
      future_gap_bound q' (fun i => hq i.succ) _ _ _ (fun ω => hf.head ω)
    calc cubeMean q (fun ω => Real.exp (lam * (f ω - cubeMean q f)))
        = coinMean (q 0) (fun b => cubeMean q' (fun ω => Real.exp (lam *
            (f (Fin.cons b ω) - cubeMean q f)))) := rfl
      _ ≤ coinMean (q 0) (fun b => Real.exp (lam * coinIncrement (q 0) M b) *
            Real.exp (lam ^ 2 * V' / K)) :=
          coinMean_mono _ (hq 0).1 (hq 0).2 _ _ hstep
      _ = coinMean (q 0) (fun b => Real.exp (lam * coinIncrement (q 0) M b)) *
            Real.exp (lam ^ 2 * V' / K) := by unfold coinMean; ring
      _ ≤ Real.exp (lam ^ 2 * (q 0 * c 0 ^ 2) / K) * Real.exp (lam ^ 2 * V' / K) := by
          gcongr
          exact coin_exp_bound _ _ _ _ (hq 0).1 (hq 0).2 hlam hlamL M hgap (hcL 0)
      _ = _ := by
          rw [← Real.exp_add, Fin.sum_univ_succ]
          congr 1
          simp only [K, V', q']
          ring

/-! ## Indicator comparison and the tails -/

/-- Markov/indicator comparison: the tail is at most `exp(-λt + λ²V/(2(1-λL)))`. -/
theorem cube_tail_le_of_lam {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) (L lam t : ℝ)
    (hcL : ∀ i, c i ≤ L) (hf : CoordBounded f c)
    (hlam : 0 ≤ lam) (hlamL : lam * L < 1) :
    cubeProb q (fun ω => t ≤ f ω - cubeMean q f) ≤
      Real.exp (-(lam * t) + lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
  classical
  have hind : ∀ ω, (if t ≤ f ω - cubeMean q f then (1 : ℝ) else 0) ≤
      Real.exp (-(lam * t)) * Real.exp (lam * (f ω - cubeMean q f)) := by
    intro ω
    rw [← Real.exp_add]
    split_ifs with h
    · apply Real.one_le_exp
      nlinarith
    · exact (Real.exp_pos _).le
  unfold cubeProb
  calc _ ≤ cubeMean q (fun ω => Real.exp (-(lam * t)) *
        Real.exp (lam * (f ω - cubeMean q f))) := cubeMean_mono q hq _ _ hind
    _ = Real.exp (-(lam * t)) * cubeMean q (fun ω => Real.exp (lam * (f ω - cubeMean q f))) :=
        cubeMean_const_mul _ _ _
    _ ≤ Real.exp (-(lam * t)) *
          Real.exp (lam ^ 2 * (∑ i, q i * c i ^ 2) / (2 * (1 - lam * L))) := by
        gcongr
        exact cube_mgf_le q hq f c L lam hcL hf hlam hlamL
    _ = _ := (Real.exp_add _ _).symm

/-- **Rare-coordinate bounded differences, upper tail.** With `V = ∑ qᵢcᵢ²`,
`P(f - Ef ≥ t) ≤ exp(-t²/(2(V+Lt)))`. The case `V = 0` is included. -/
theorem cube_upper_tail {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordBounded f c) (t : ℝ) (ht : 0 < t) :
    cubeProb q (fun ω => t ≤ f ω - cubeMean q f) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  set V := ∑ i, q i * c i ^ 2 with hVdef
  have hV0 : 0 ≤ V := Finset.sum_nonneg fun i _ =>
    mul_nonneg (hq i).1 (sq_nonneg _)
  have hcL : ∀ i, c i ≤ L := fun i => (hc i).2
  rcases hV0.lt_or_eq with hV | hV
  · -- `λ = t / (V + L t)`
    have hD : 0 < V + L * t := by positivity
    set lam := t / (V + L * t)
    have hlam : 0 ≤ lam := by positivity
    have hlamL : lam * L < 1 := by
      rw [div_mul_eq_mul_div, div_lt_one hD]; nlinarith
    refine (cube_tail_le_of_lam q hq f c L lam t hcL hf hlam hlamL).trans
      (le_of_eq (congrArg Real.exp ?_))
    have h1 : 1 - lam * L = V / (V + L * t) := by
      simp only [lam]; field_simp; ring
    rw [h1]
    simp only [lam]
    field_simp
    ring
  · -- `V = 0`: `λ = 1/(2L)` already gives the stated bound.
    have hlamL : 1 / (2 * L) * L < 1 := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]; linarith
    refine (cube_tail_le_of_lam q hq f c L (1 / (2 * L)) t hcL hf (by positivity)
      hlamL).trans (le_of_eq (congrArg Real.exp ?_))
    rw [← hVdef, ← hV]
    field_simp
    ring

/-- **Rare-coordinate bounded differences, lower tail.**
`P(Ef - f ≥ t) ≤ exp(-t²/(2(V+Lt)))`, including `V = 0`. -/
theorem cube_lower_tail {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (f : (Fin n → Bool) → ℝ) (c : Fin n → ℝ) (L : ℝ) (hL : 0 < L)
    (hc : ∀ i, 0 ≤ c i ∧ c i ≤ L) (hf : CoordBounded f c) (t : ℝ) (ht : 0 < t) :
    cubeProb q (fun ω => t ≤ cubeMean q f - f ω) ≤
      Real.exp (-(t ^ 2 / (2 * ((∑ i, q i * c i ^ 2) + L * t)))) := by
  have h := cube_upper_tail q hq (fun ω => -f ω) c L hL hc hf.neg t ht
  rw [cubeMean_neg] at h
  convert h using 3
  constructor <;> intro h' <;> linarith

end PartitionedTriangleAbsorption.BernoulliConcentration
