/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedRoundStage172

/-! # A type-rich first round from near-unit loads

The load tolerance is explicit; the type collision budget uses the uniform
upper bound 5/4, not a silently normalized fractional decomposition.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedNearRoundStage174

open Finset BernoulliExposure BernoulliConcentration Nibble
  TypedSupplyStage171 TypedRoundStage172

theorem near_round_failure_lt (b δ γ θ ε u : ℝ) (hb : 0 < b)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1 / 128) (hθ : 0 < θ) (hε : 0 < ε) (hu : 0 < u) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ),
      (∀ i, Nibble.triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
      (∀ i, w i ≤ b / Fintype.card V) → (∀ e ∈ B, |S.load w e - 1| ≤ δ) →
      cubeProb (qv γ w)
        (fun ω => ¬ RoundGood S B w (b / Fintype.card V) δ γ θ ε ω) < u := by
  obtain ⟨N0, hN0⟩ := eventually_failBound_lt b γ θ ε u hb hγ (by linarith) hθ hε hu
  refine ⟨max (max N0 1) ⌈4 * γ * b⌉₊, ?_⟩
  intro V _ _ hN m S B w hB hw hwb hload
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hceil : 4 * γ * b ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have H : RoundHyp S B w (b / Fintype.card V) δ γ :=
    { hB := hB, w0 := hw, wβ := hwb, β0 := by positivity
      load_lo := fun e he => by have h := (abs_le.mp (hload e he)).1; linarith
      load_hi := fun e he => by have h := (abs_le.mp (hload e he)).2; linarith
      δ0 := hδ0, δ1 := hδ1, γ0 := hγ, γ1 := hγ1
      γβ := by rw [mul_div_assoc', div_le_iff₀ hnpos]; nlinarith }
  exact (H.round_fail_le θ ε hθ hε _ (sqrt_sqrt_bounds _ hn1).1).trans_lt
    (hN0 _ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) b hb le_rfl)

theorem first_round_supply_near {ι : Type} [Fintype ι] [Nonempty ι]
    (b δ γ θ ε a : ℝ) (hb : 0 < b) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 4)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 128) (hθ : 0 < θ) (hε : 0 < ε) (ha : 0 < a)
    (hγtypes : γ ≤ 1 / (192 * Fintype.card ι)) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
        (J : ι → Finset (Fin m)),
      (∀ i, Nibble.triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
      (∀ i, w i ≤ b / Fintype.card V) → (∀ e ∈ B, |S.load w e - 1| ≤ δ) →
      (∀ t, a * (Fintype.card V : ℝ) ^ 2 ≤ ∑ i ∈ J t, w i) →
      ∃ ω, RoundGood S B w (b / Fintype.card V) δ γ θ ε ω ∧
        ∀ t, γ * a * (Fintype.card V : ℝ) ^ 2 / 4 ≤ (J t ∩ S.packing ω).card := by
  obtain ⟨N0, hN0⟩ := near_round_failure_lt b δ γ θ ε (1 / 4)
    hb hδ0 hδ1 hγ hγ1 hθ hε (by norm_num)
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
  have hglobal : ∀ e ∈ univ.biUnion (fun i => Nibble.triEdges (S.tri i)),
      S.load w e ≤ 5 / 4 := by
    intro e he
    obtain ⟨i, _, hi⟩ := mem_biUnion.mp he
    have h := (abs_le.mp (hload e (hB i hi))).2
    linarith
  have hbudget : cubeProb (fun i => γ * w i)
      (fun ω => ¬ RoundGood S B w (b / Fintype.card V) δ γ θ ε ω) +
      ∑ t, (Real.exp (-(∑ i ∈ J t, γ * w i) / 12) + 12 * γ * (5 / 4)) < 1 := by
    have hfail := hN0 V hN0' m S B w hB hw hwb hload
    have hsum : ∑ t, (Real.exp (-(∑ i ∈ J t, γ * w i) / 12) +
        12 * γ * (5 / 4)) ≤ 1 / 4 := by
      have hs := sum_le_sum (s := (univ : Finset ι)) (fun t _ =>
        add_le_add_right (exponential_budget _ _ hr (hμ t)) (12 * γ * (5 / 4)))
      simp only [sum_const, card_univ, nsmul_eq_mul] at hs
      simp only [add_comm (12 * γ * (5 / 4))] at hs
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 192 * Fintype.card ι)] at hγtypes
      have hid : (Fintype.card ι : ℝ) * (1 / (8 * Fintype.card ι)) = 1 / 8 := by field_simp
      nlinarith
    have hfail' : cubeProb (fun i => γ * w i)
        (fun ω => ¬ RoundGood S B w (b / Fintype.card V) δ γ θ ε ω) < 1 / 4 := hfail
    linarith
  obtain ⟨ω, hg, hs⟩ := exists_supply_and_good S J w γ (5 / 4) hγ.le hw hq hglobal
    (fun t => lt_of_lt_of_le (by positivity) (hμ t))
    (RoundGood S B w (b / Fintype.card V) δ γ θ ε) hbudget
  refine ⟨ω, hg, fun t => ?_⟩
  have hm := mul_le_mul_of_nonneg_left (hmass t) hγ.le
  rw [mul_sum] at hm
  exact (div_le_div_of_nonneg_right (by nlinarith : γ * a * (Fintype.card V : ℝ) ^ 2 ≤
    ∑ i ∈ J t, γ * w i) (by norm_num : (0 : ℝ) ≤ 4)).trans (hs t)

end PartitionedTriangleAbsorption.TypedNearRoundStage174

