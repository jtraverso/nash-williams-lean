/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.EffectiveRound

@[expose] public section

/-!
# The nibble with fixed explicit schedule and threshold

All parameters below are actual definitions. No qualitative sufficiently-large
threshold is chosen after the density. The packing proof uses the original
round invariant and its proved step.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open Finset KeevashQuantitative

noncomputable def packingThreshold (b ζ : ℝ) : ℕ :=
  max (max (physicalRoundThreshold (scheduledWeightCap b ζ)
    (scheduleGamma ζ) (commonRate b ζ)) 1)
    ⌈10 * scheduleGamma ζ * scheduledWeightCap b ζ / loadTolerance ζ⌉₊

theorem nibble_packing_near_effective (b η ξ : ℝ) (hb : 0 < b)
    (hη : 0 < η) (hξ : 0 < ξ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V],
      packingThreshold b (min η (min 1 (ξ ^ 2))) ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ),
        (∀ i, triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
        (∀ i, w i ≤ b / Fintype.card V) →
        (∀ v, ((star B v).card : ℝ) ≤ (1 - ξ) * Fintype.card V) →
        (∀ e ∈ B, |S.load w e - 1| ≤ loadTolerance (min η (min 1 (ξ ^ 2)))) →
        ∃ P : Finset (Fin m), IsPacking S P ∧
          ∀ v, ((star (B \ edgesOf S P) v).card : ℝ) ≤ η * Fintype.card V := by
  let ζ := min η (min 1 (ξ ^ 2))
  have hζ : 0 < ζ := lt_min hη (lt_min (by norm_num) (sq_pos_of_pos hξ))
  have hζη : ζ ≤ η := min_le_left _ _
  have hζ1 : ζ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hζξ : ζ ≤ ξ ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  let γ := scheduleGamma ζ
  let r := scheduleRounds ζ
  have hγ0 : 0 < γ := scheduleGamma_pos ζ hζ
  have hγ1 : γ ≤ 1 / 128 := scheduleGamma_le ζ hζ hζ1
  have hr1 : 1 ≤ r := schedule_rounds_pos ζ hζ hζ1
  have hdeg : (1 - γ / 8) ^ r ≤ ζ / 2 := schedule_decay ζ hζ hζ1
  have hwaste : 24 * (r : ℝ) * γ ^ 2 ≤ ζ / 4 := schedule_waste ζ hζ hζ1
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr1
  have hγξ : γ / 8 ≤ ξ := by
    have hsq : γ ^ 2 ≤ ξ ^ 2 := by nlinarith [sq_nonneg γ]
    nlinarith
  let a : ℝ := 1 + 5 * γ
  have ha1 : 1 ≤ a := by dsimp [a]; linarith
  let c : ℝ := 1 / (8 * r * a ^ r)
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hcr : c * r * a ^ r = 1 / 8 := by dsimp [c]; field_simp
  have hc1 : c ≤ 1 / 4 := by
    have hp : 1 ≤ a ^ r := one_le_pow₀ ha1
    have h1 : c ≤ c * r := le_mul_of_one_le_right hc0.le hrR
    have h2 : c * r ≤ c * r * a ^ r := le_mul_of_one_le_right (by positivity) hp
    linarith
  let bmax : ℝ := b * Real.exp (2 * γ * r)
  have hbmax : 0 < bmax := by dsimp [bmax]; positivity
  let rate := commonRate b ζ
  have hrate : 0 < rate := commonRate_pos b ζ hb.le hζ
  have hrates : RateBounds bmax γ (ζ / 2) (c / 2) rate :=
    commonRate_bounds b ζ hb hζ hζ1
  let N0 := physicalRoundThreshold bmax γ rate
  have hN0 := near_load_round_at_rate bmax γ (ζ / 2) (c / 2) rate
    hγ0 hγ1 (by positivity) (by positivity) hrate hrates
  intro V _ _ hN m S B w hB hw0 hwb hcap hload
  change max (max N0 1) ⌈10 * γ * bmax / c⌉₊ ≤ Fintype.card V at hN
  change ∀ e ∈ B, |S.load w e - 1| ≤ c at hload
  have hN0' : N0 ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnpos : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn1
  have hnbig : 10 * γ * bmax / c ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  rw [div_le_iff₀ hc0] at hnbig
  let w' : Fin m → ℝ := fun i => Real.exp (-2 * γ) * w i
  have hw'0 : ∀ i, 0 ≤ w' i := fun i => mul_nonneg (Real.exp_pos _).le (hw0 i)
  have hw'b : ∀ i, w' i ≤ b / Fintype.card V := by
    intro i
    apply le_trans (b := w i) _ (hwb i)
    have he : Real.exp (-2 * γ) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    simpa [w'] using mul_le_mul_of_nonneg_right he (hw0 i)
  have key : ∀ j, 1 ≤ j → j ≤ r →
      ∃ (s : Finset (Fin m)) (Bj W : Finset (Sym2 V)) (P : Finset (Fin m)),
        IterInv S B w' γ (ζ / 2) c a j s Bj W P := by
    intro j
    induction j with
    | zero => omega
    | succ j ih =>
      intro hj1 hjr
      by_cases hj : j = 0
      · subst j
        refine ⟨_, _, _, _, IterInv.start_near S B w γ (ζ / 2) c a hB ?_ ?_⟩
        · intro v
          exact (hcap v).trans (mul_le_mul_of_nonneg_right (by linarith) hnpos.le)
        · intro e he
          exact (hload e he).trans (le_mul_of_one_le_right hc0.le ha1)
      obtain ⟨s, Bj, W, P, hI⟩ := ih (by omega) (by omega)
      have hjrR : (j : ℝ) ≤ r := by exact_mod_cast (by omega : j ≤ r)
      let bj : ℝ := b * Real.exp (2 * γ * j)
      have hbj0 : 0 < bj := by dsimp [bj]; positivity
      have hbjmax : bj ≤ bmax :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hb.le
      have hδ0 : 0 ≤ c * j * a ^ j := by positivity
      have hδ1 : c * j * a ^ j ≤ 1 / 4 := by
        have h1 : a ^ j ≤ a ^ r := pow_le_pow_right₀ ha1 (by omega)
        have h2 : c * j ≤ c * r := mul_le_mul_of_nonneg_left hjrR hc0.le
        have h3 : c * j * a ^ j ≤ c * r * a ^ r :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
        linarith
      have hβ : 5 * γ * (bj / Fintype.card V) ≤ c / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hnpos]
        have : γ * bj ≤ γ * bmax := mul_le_mul_of_nonneg_left hbjmax hγ0.le
        nlinarith
      obtain ⟨-, ω, -, hgood, -⟩ := hN0 V hN0' s.card (S.reindex s) Bj
        (fun k => Real.exp (2 * γ * j) * w' (reidx s k)) bj (c * j * a ^ j)
        hbj0 hbjmax hδ0 hδ1 (fun k => hI.alive_sub _ (reidx_mem s k))
        (fun k => mul_nonneg (Real.exp_pos _).le (hw'0 _))
        (fun k => by
          calc Real.exp (2 * γ * j) * w' (reidx s k)
              ≤ Real.exp (2 * γ * j) * (b / Fintype.card V) :=
                mul_le_mul_of_nonneg_left (hw'b _) (Real.exp_pos _).le
            _ = bj / Fintype.card V := by dsimp [bj]; ring)
        (fun e he => by
          have h := hI.load e he
          rw [reindex_load S s (fun i => Real.exp (2 * γ * j) * w' i) e]
          unfold aliveLoad at h
          exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩)
      exact ⟨_, _, _, _, hI.step hγ0.le (by linarith) (by rfl) hc0.le ω _ hβ hgood⟩
  obtain ⟨s, Bj, W, P, hI⟩ := key r hr1 le_rfl
  refine ⟨P, hI.pack, fun v => ?_⟩
  have h1 : (star (B \ edgesOf S P) v).card ≤ (star Bj v).card + (star W v).card :=
    (card_le_card (star_mono hI.cover v)).trans (card_star_union_le _ _ v)
  have h1R : ((star (B \ edgesOf S P) v).card : ℝ) ≤ (star Bj v).card + (star W v).card := by
    exact_mod_cast h1
  have h2 : ((star Bj v).card : ℝ) ≤ ζ / 2 * Fintype.card V := by
    rcases hI.deg v with h | h
    · exact h.le
    · exact h.trans (mul_le_mul_of_nonneg_right hdeg hnpos.le)
  have h3 : ((star W v).card : ℝ) ≤ ζ / 4 * Fintype.card V := by
    refine (hI.waste v).trans ?_
    have := mul_le_mul_of_nonneg_right hwaste hnpos.le
    linarith
  have := mul_le_mul_of_nonneg_right hζη hnpos.le
  nlinarith


#print axioms nibble_packing_near_effective

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
