/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.NearConsumer
public import PartitionedTriangleAbsorption.BlowupB.PaddedQuantitative.EffectiveRate
public import PartitionedTriangleAbsorption.BlowupB.PaddedQuantitative.EffectiveTail

@[expose] public section

/-!
# An explicit threshold for the physical nibble round

The probabilistic estimates are those of the supplied nibble. The nine
rates and the exponential-tail threshold are explicit inputs, so their
dependence on a variable density can be bounded before choosing that density.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open Finset KeevashQuantitative BernoulliExposure BernoulliConcentration

def RateBounds (bmax γ θ ε c : ℝ) : Prop :=
  c ≤ γ * θ / 64 ∧ c ≤ θ / (24576 * bmax * (γ + 1 / 64)) ∧
  c ≤ γ * θ / 128 ∧ c ≤ γ * θ / 4704 ∧ c ≤ γ / (12 * bmax) ∧
  c ≤ γ ^ 2 / 2 ∧ c ≤ γ ^ 3 / 4 ∧ c ≤ 1 / 8 ∧
  c ≤ (ε / 2) ^ 2 / (2 * (10 * bmax * γ + 3 * bmax * (ε / 2)))

noncomputable def failureThreshold (c : ℝ) : ℕ :=
  max 1 ((tailThreshold c 2560 8) ^ 4)

noncomputable def physicalRoundThreshold (bmax γ c : ℝ) : ℕ :=
  max (max (failureThreshold c) 1) ⌈4 * γ * bmax⌉₊

theorem failBound_at_rate (bmax γ θ ε c : ℝ)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hθ : 0 < θ) (hε : 0 < ε)
    (hc : 0 < c) (hrate : RateBounds bmax γ θ ε c) :
    ∀ n : ℕ, failureThreshold c ≤ n → ∀ b : ℝ, 0 < b → b ≤ bmax →
      failBound n (Nat.sqrt (Nat.sqrt n)) (b / n) γ θ ε < 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hrate
  let k0 := tailThreshold c 2560 8
  have hk0 (k : ℕ) (hk : k0 ≤ k) :
      2560 * (k : ℝ) ^ 8 * Real.exp (-(c * k)) < 1 :=
    nibble_tail_explicit c hc k hk
  intro n hn b hb hbb
  change max 1 (k0 ^ 4) ≤ n at hn
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
  linarith


theorem near_load_round_at_rate (bmax γ θ ε c : ℝ) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1 / 128) (hθ : 0 < θ) (hε : 0 < ε)
    (hc : 0 < c) (hrate : RateBounds bmax γ θ ε c) :
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      physicalRoundThreshold bmax γ c ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ) (b δ : ℝ),
        0 < b → b ≤ bmax → 0 ≤ δ → δ ≤ 1 / 4 →
        (∀ i, triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
        (∀ i, w i ≤ b / Fintype.card V) →
        (∀ e ∈ B, 1 - δ ≤ S.load w e ∧ S.load w e ≤ 1 + δ) →
        cubeProb (qv γ w)
            (fun ω => ¬ RoundGood S B w (b / Fintype.card V) δ γ θ ε ω) < 1 ∧
          ∃ ω : Fin m → Bool, 0 < cubeWeight (qv γ w) ω ∧
            RoundGood S B w (b / Fintype.card V) δ γ θ ε ω ∧
            B \ S.packEdges ω = S.untouched B ω ∪ S.waste ω ∧
            Disjoint (S.untouched B ω) (S.waste ω) := by
  let N0 := failureThreshold c
  have hN0 := failBound_at_rate bmax γ θ ε c hγ0 (by linarith) hθ hε hc hrate
  intro V _ _ hN m S B w b δ hb hbb hδ0 hδ1 hB hw0 hwb hload
  change max (max N0 1) ⌈4 * γ * bmax⌉₊ ≤ Fintype.card V at hN
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hceil : 4 * γ * bmax ≤ Fintype.card V := by
    have := le_trans (le_max_right _ _) hN
    exact (Nat.le_ceil _).trans (by exact_mod_cast this)
  have H : RoundHyp S B w (b / Fintype.card V) δ γ :=
    { hB := hB
      w0 := hw0
      wβ := hwb
      β0 := by positivity
      load_lo := fun e he => (hload e he).1
      load_hi := fun e he => (hload e he).2
      δ0 := hδ0
      δ1 := hδ1
      γ0 := hγ0
      γ1 := hγ1
      γβ := by
        rw [mul_div_assoc', div_le_iff₀ hnpos]
        nlinarith }
  have hK : 1 ≤ Nat.sqrt (Nat.sqrt (Fintype.card V)) := (sqrt_sqrt_bounds _ hn1).1
  have hfail := (H.round_fail_le θ ε hθ hε _ hK).trans_lt
    (hN0 _ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) b hb hbb)
  refine ⟨hfail, ?_⟩
  obtain ⟨ω, hpos, hgood⟩ := exists_pos_weight_of_cubeProb_lt_one _ H.hq _ hfail
  push Not at hgood
  exact ⟨ω, hpos, hgood, S.residual_identity B hB ω⟩


#print axioms failBound_at_rate
#print axioms near_load_round_at_rate

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
