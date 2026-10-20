/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedSupplyStage171

/-! # A good first nibble round with type supply

The graph order threshold is chosen before the physical triangle system. The
input type supply is fractional mass, not counts in an assumed integral packing.
The accepted failure-bound calculation is reused with a variable tolerance.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRoundStage172

open Finset BernoulliExposure BernoulliConcentration Nibble TypedSupplyStage171

/-- The accepted explicit failure estimate tends to zero, not merely below one. -/
theorem eventually_failBound_lt (bmax γ θ ε u : ℝ) (hbmax : 0 < bmax) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1) (hθ : 0 < θ) (hε : 0 < ε) (hu : 0 < u) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ b : ℝ, 0 < b → b ≤ bmax →
      failBound n (Nat.sqrt (Nat.sqrt n)) (b / n) γ θ ε < u := by
  obtain ⟨c, hc, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ : ∃ c : ℝ, 0 < c ∧
      c ≤ γ * θ / 64 ∧ c ≤ θ / (24576 * bmax * (γ + 1 / 64)) ∧ c ≤ γ * θ / 128 ∧
      c ≤ γ * θ / 4704 ∧ c ≤ γ / (12 * bmax) ∧ c ≤ γ ^ 2 / 2 ∧ c ≤ γ ^ 3 / 4 ∧ c ≤ 1 / 8 ∧
      c ≤ (ε / 2) ^ 2 / (2 * (10 * bmax * γ + 3 * bmax * (ε / 2))) := by
    refine ⟨_, ?_, c_bounds⟩
    simp only [lt_min_iff]
    refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_, ?_⟩ <;> positivity
  obtain ⟨k0, hk0⟩ := exists_pow_mul_exp_lt c (2560 / u) hc (by positivity)
  refine ⟨max 1 (k0 ^ 4), fun n hn b hb hbb => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_left _ _) hn
  obtain ⟨hk1, hk4, hk16⟩ := sqrt_sqrt_bounds n hn1
  have hkk0 : k0 ≤ Nat.sqrt (Nat.sqrt n) := by
    have : k0 ^ 4 ≤ n := le_trans (le_max_right _ _) hn
    have h1 : k0 * k0 ≤ Nat.sqrt n := Nat.le_sqrt.mpr (by nlinarith)
    exact Nat.le_sqrt.mpr h1
  have hK := hk0 _ hkk0
  generalize Nat.sqrt (Nat.sqrt n) = k at hk1 hk4 hk16 hK ⊢
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hk4R : (k : ℝ) ^ 4 ≤ n := by exact_mod_cast hk4
  have hk16R : (n : ℝ) ≤ 16 * (k : ℝ) ^ 4 := by exact_mod_cast hk16
  have hnk : (k : ℝ) ≤ n := by nlinarith [pow_le_pow_right₀ hkR (by norm_num : 1 ≤ 4)]
  have hk0' : (0 : ℝ) ≤ k := by linarith
  have hsum := failBound_le_of_terms n k (b / n) γ θ ε (Real.exp (-(c * k))) hnR
    (rate_lin h1 hc hk0' hnk (le_of_eq (by ring)))
    (rate_lin h2 hc hk0' hnk (alg2 hθ hγ hb hbb hnR))
    (rate_lin h3 hc hk0' hnk (le_of_eq (by ring)))
    (rate_sq h4 hc hkR (alg4 hγ hθ hkR hk4R))
    (rate_lin h5 hc hk0' hnk (alg5 hγ hb hbb hnR))
    (rate_lin h6 hc hk0' hnk (le_of_eq (by ring)))
    (rate_sq h7 hc hkR (alg7 hγ hγ1 hkR hk4R))
    (Real.exp_le_exp.mpr (by
      have := mul_le_mul_of_nonneg_right h8 hk0'
      linarith))
    (rate_lin h9 hc hk0' hnk (alg9 hε hγ hb hbb hnR))
  have hfin : 10 * (n : ℝ) ^ 2 * Real.exp (-(c * k)) ≤
      2560 * (k : ℝ) ^ 8 * Real.exp (-(c * k)) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 : (n : ℝ) ^ 2 ≤ (16 * (k : ℝ) ^ 4) ^ 2 := pow_le_pow_left₀ (by linarith) hk16R 2
    nlinarith
  have heq : 2560 * (k : ℝ) ^ 8 * Real.exp (-(c * k)) =
      u * ((2560 / u) * (k : ℝ) ^ 8 * Real.exp (-(c * k))) := by field_simp
  exact hsum.trans_lt (hfin.trans_lt (by rw [heq]; nlinarith))

theorem exact_round_failure_lt (b γ θ ε u : ℝ) (hb : 0 < b) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1 / 128) (hθ : 0 < θ) (hε : 0 < ε) (hu : 0 < u) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ),
      (∀ i, Nibble.triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
      (∀ i, w i ≤ b / Fintype.card V) → (∀ e ∈ B, S.load w e = 1) →
      cubeProb (qv γ w)
        (fun ω => ¬ RoundGood S B w (b / Fintype.card V) 0 γ θ ε ω) < u := by
  obtain ⟨N0, hN0⟩ := eventually_failBound_lt b γ θ ε u hb hγ (by linarith) hθ hε hu
  refine ⟨max (max N0 1) ⌈4 * γ * b⌉₊, ?_⟩
  intro V _ _ hN m S B w hB hw hwb hload
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hceil : 4 * γ * b ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have H : RoundHyp S B w (b / Fintype.card V) 0 γ :=
    { hB := hB, w0 := hw, wβ := hwb, β0 := by positivity
      load_lo := fun e he => by simp [hload e he]
      load_hi := fun e he => by simp [hload e he]
      δ0 := le_rfl, δ1 := by norm_num, γ0 := hγ, γ1 := hγ1
      γβ := by rw [mul_div_assoc', div_le_iff₀ hnpos]; nlinarith }
  exact (H.round_fail_le θ ε hθ hε _ (sqrt_sqrt_bounds _ hn1).1).trans_lt
    (hN0 _ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) b hb le_rfl)

theorem exponential_budget (r μ : ℝ) (hr : 0 < r) (hμ : 96 * r ≤ μ) :
    Real.exp (-μ / 12) ≤ 1 / (8 * r) := by
  have he := Real.add_one_le_exp (μ / 12)
  have hprod : Real.exp (-μ / 12) * Real.exp (μ / 12) = 1 := by
    rw [← Real.exp_add, show -μ / 12 + μ / 12 = 0 by ring, Real.exp_zero]
  rw [le_div_iff₀ (by positivity : 0 < 8 * r)]
  have hbound : 8 * r ≤ Real.exp (μ / 12) := by linarith
  nlinarith [Real.exp_pos (-μ / 12)]

/-- Type counts and all three accepted round conclusions hold for the same outcome. -/
theorem first_round_supply {ι : Type} [Fintype ι] [Nonempty ι]
    (b γ θ ε a : ℝ) (hb : 0 < b) (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 128)
    (hθ : 0 < θ) (hε : 0 < ε) (ha : 0 < a)
    (hγtypes : γ ≤ 1 / (96 * Fintype.card ι)) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
        (J : ι → Finset (Fin m)),
      (∀ i, Nibble.triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
      (∀ i, w i ≤ b / Fintype.card V) → (∀ e ∈ B, S.load w e = 1) →
      (∀ t, a * (Fintype.card V : ℝ) ^ 2 ≤ ∑ i ∈ J t, w i) →
      ∃ ω, RoundGood S B w (b / Fintype.card V) 0 γ θ ε ω ∧
        ∀ t, γ * a * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (J t ∩ S.packing ω).card := by
  obtain ⟨N0, hN0⟩ := exact_round_failure_lt b γ θ ε (1 / 4) hb hγ hγ1 hθ hε (by norm_num)
  refine ⟨max (max N0 1) (max ⌈4 * γ * b⌉₊ ⌈96 * Fintype.card ι / (γ * a)⌉₊), ?_⟩
  intro V _ _ hN m S B w J hB hw hwb hload hmass
  have hN0' : N0 ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hr : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hceil : 4 * γ * b ≤ Fintype.card V := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have hnlarge : 96 * Fintype.card ι / (γ * a) ≤ Fintype.card V := (Nat.le_ceil _).trans
    (by exact_mod_cast le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  rw [div_le_iff₀ (mul_pos hγ ha)] at hnlarge
  have hμ : ∀ t, 96 * Fintype.card ι ≤ ∑ i ∈ J t, γ * w i := by
    intro t
    rw [← mul_sum]
    have hm := mul_le_mul_of_nonneg_left (hmass t) hγ.le
    have hn2 : (Fintype.card V : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hq : ∀ i, 0 ≤ γ * w i ∧ γ * w i ≤ 1 := by
    intro i
    refine ⟨mul_nonneg hγ.le (hw i), ?_⟩
    have h := mul_le_mul_of_nonneg_left (hwb i) hγ.le
    rw [mul_div_assoc', le_div_iff₀ hnpos] at h
    nlinarith
  have hglobal : ∀ e ∈ univ.biUnion (fun i => Nibble.triEdges (S.tri i)), S.load w e ≤ 1 := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    exact (hload e (hB i hi)).le
  have hbudget : cubeProb (fun i => γ * w i)
      (fun ω => ¬ RoundGood S B w (b / Fintype.card V) 0 γ θ ε ω) +
      ∑ t, (Real.exp (-(∑ i ∈ J t, γ * w i) / 12) + 12 * γ * 1) < 1 := by
    have hfail := hN0 V hN0' m S B w hB hw hwb hload
    have hsum : ∑ t, (Real.exp (-(∑ i ∈ J t, γ * w i) / 12) + 12 * γ * 1) ≤ 1 / 4 := by
      have hs := sum_le_sum (s := (univ : Finset ι)) (fun t _ =>
        add_le_add_right (exponential_budget _ _ hr (hμ t)) (12 * γ * 1))
      simp only [sum_const, card_univ, nsmul_eq_mul] at hs
      simp only [add_comm (12 * γ * 1)] at hs
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 96 * Fintype.card ι)] at hγtypes
      have hid : (Fintype.card ι : ℝ) * (1 / (8 * Fintype.card ι)) = 1 / 8 := by field_simp
      nlinarith
    have hfail' : cubeProb (fun i => γ * w i)
        (fun ω => ¬ RoundGood S B w (b / Fintype.card V) 0 γ θ ε ω) < 1 / 4 := hfail
    linarith
  obtain ⟨ω, hg, hs⟩ := exists_supply_and_good S J w γ 1 hγ.le hw hq hglobal
    (fun t => lt_of_lt_of_le (by positivity) (hμ t))
    (RoundGood S B w (b / Fintype.card V) 0 γ θ ε) hbudget
  refine ⟨ω, hg, fun t => ?_⟩
  have hm := mul_le_mul_of_nonneg_left (hmass t) hγ.le
  rw [mul_sum] at hm
  exact (div_le_div_of_nonneg_right (by nlinarith : γ * a * (Fintype.card V : ℝ) ^ 2 ≤
    ∑ i ∈ J t, γ * w i) (by norm_num : (0 : ℝ) ≤ 4)).trans (hs t)

end PartitionedTriangleAbsorption.TypedRoundStage172

