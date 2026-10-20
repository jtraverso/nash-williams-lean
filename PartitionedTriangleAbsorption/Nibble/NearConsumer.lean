/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.Consumer

/-! # Nibble from approximate loads with an explicit degree gap

The initial error is chosen before the graph. A positive gap in the initial
maximum degree permits starting the accepted invariant at time one. The
weights are shifted back by `exp (-2γ)`; all subsequent rounds use the existing
`IterInv.step`, not a second implementation of the probabilistic argument.
This produces a packing, not an absorber or a decomposition of the whole graph.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open Finset

theorem IterInv.start_near {V : Type} [Fintype V] [DecidableEq V] {m : ℕ}
    (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (γ θ c a : ℝ) (hB : ∀ i, triEdges (S.tri i) ⊆ B)
    (hdeg : ∀ v, ((star B v).card : ℝ) ≤ (1 - γ / 8) * Fintype.card V)
    (hload : ∀ e ∈ B, |S.load w e - 1| ≤ c * a) :
    IterInv S B (fun i => Real.exp (-2 * γ) * w i) γ θ c a 1 univ B ∅ ∅ where
  alive_sub i _ := hB i
  pack := by simp [IsPacking]
  disj := by simp [edgesOf]
  cover := by simp [edgesOf]
  waste v := by
    simp only [star, filter_empty, card_empty, Nat.cast_zero, Nat.cast_one, mul_one]
    positivity
  deg v := Or.inr (by simpa using hdeg v)
  load e he := by
    have hw : ∀ i, Real.exp (2 * γ) * (Real.exp (-2 * γ) * w i) = w i := by
      intro i
      rw [← mul_assoc, ← Real.exp_add]
      simp
    simp only [Nat.cast_one, mul_one, pow_one, aliveLoad, hw]
    exact hload e he

/-- Near-unit loads suffice. The positive degree gap is an explicit premise;
it is not inferred from the weighting or from divisibility. -/
theorem nibble_packing_near (b η ξ : ℝ) (hb : 0 < b) (hη : 0 < η)
    (hξ : 0 < ξ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ),
        (∀ i, triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
        (∀ i, w i ≤ b / Fintype.card V) →
        (∀ v, ((star B v).card : ℝ) ≤ (1 - ξ) * Fintype.card V) →
        (∀ e ∈ B, |S.load w e - 1| ≤ δ) →
        ∃ P : Finset (Fin m), IsPacking S P ∧
          ∀ v, ((star (B \ edgesOf S P) v).card : ℝ) ≤ η * Fintype.card V := by
  let ζ := min η (min 1 (ξ ^ 2))
  have hζ : 0 < ζ := lt_min hη (lt_min (by norm_num) (sq_pos_of_pos hξ))
  have hζη : ζ ≤ η := min_le_left _ _
  have hζ1 : ζ ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  have hζξ : ζ ≤ ξ ^ 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨γ, r, hγ0, hγ1, hr1, hdeg, hwaste⟩ := schedule_params ζ hζ hζ1
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
  obtain ⟨N0, hN0⟩ := near_load_round bmax γ (ζ / 2) (c / 2) hbmax hγ0 hγ1
    (by positivity) (by positivity)
  refine ⟨c, hc0, hc1, max (max N0 1) ⌈10 * γ * bmax / c⌉₊, ?_⟩
  intro V _ _ hN m S B w hB hw0 hwb hcap hload
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

end PartitionedTriangleAbsorption.Nibble
