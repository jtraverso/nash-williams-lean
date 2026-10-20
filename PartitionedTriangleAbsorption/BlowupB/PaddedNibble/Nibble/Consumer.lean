/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.Iterate

/-! # The ordinary nibble consumer

For fixed `b > 0` and `0 < η ≤ 1` there is `N` such that for every vertex set of
size `n ≥ N`, every family of distinct physical triangles of a graph `B`
(all three edges in `B`), with weights `0 ≤ w ≤ b/n` and exact unit load on every
edge of `B`, admits an actual edge-disjoint triangle packing `P` whose residual
graph `B \ E(P)` has maximum degree at most `η n`.

The proof runs `r` rounds of `near_load_round` (each in a fresh finite product
space on the current surviving system) with the schedule from `schedule_params`,
and maintains `IterInv`. This does NOT produce a fractional weighting on an
arbitrary dense graph and does NOT establish typed absorption.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/Nibble/Consumer.lean.
Original SHA256: 2d6dc2d5ed2a002ce21a818125804914293c2dce6139a44c740d11de73f77aa3.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open BernoulliExposure BernoulliConcentration Finset

/-- **Nibble packing from a near-uniform unit-load triangle weighting.** -/
theorem nibble_packing (b η : ℝ) (hb : 0 < b) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (m : ℕ) (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ),
        (∀ i, triEdges (S.tri i) ⊆ B) → (∀ i, 0 ≤ w i) →
        (∀ i, w i ≤ b / Fintype.card V) → (∀ e ∈ B, S.load w e = 1) →
        ∃ P : Finset (Fin m), IsPacking S P ∧
          ∀ v, ((star (B \ edgesOf S P) v).card : ℝ) ≤ η * Fintype.card V := by
  obtain ⟨γ, r, hγ0, hγ1, hr1, hdeg, hwaste⟩ := schedule_params η hη0 hη1
  set a : ℝ := 1 + 5 * γ with ha
  have ha1 : 1 ≤ a := by rw [ha]; linarith
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  set c : ℝ := 1 / (8 * r * a ^ r) with hc
  have hapos : 0 < a ^ r := by positivity
  have hc0 : 0 < c := by positivity
  have hcr : c * r * a ^ r = 1 / 8 := by rw [hc]; field_simp
  set bmax : ℝ := b * Real.exp (2 * γ * r) with hbmax
  have hbmax0 : 0 < bmax := by positivity
  obtain ⟨N0, hN0⟩ := near_load_round bmax γ (η / 2) (c / 2) hbmax0 hγ0 hγ1 (by positivity)
    (by positivity)
  refine ⟨max (max N0 1) ⌈10 * γ * bmax / c⌉₊, ?_⟩
  intro V _ _ hN m S B w hB hw0 hwb hload
  have hN0' : N0 ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hn1 : 1 ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hnR : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn1
  have hnpos : (0 : ℝ) < Fintype.card V := by linarith
  have hnbig : 10 * γ * bmax / c ≤ Fintype.card V :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  rw [div_le_iff₀ hc0] at hnbig
  have key : ∀ j, j ≤ r → ∃ (s : Finset (Fin m)) (Bj W : Finset (Sym2 V)) (P : Finset (Fin m)),
      IterInv S B w γ (η / 2) c a j s Bj W P := by
    intro j
    induction j with
    | zero => intro _; exact ⟨_, _, _, _, IterInv.start S B w γ (η / 2) c a hB hload⟩
    | succ j ih =>
      intro hj
      obtain ⟨s, Bj, W, P, hI⟩ := ih (by omega)
      have hjr : (j : ℝ) ≤ r := by exact_mod_cast (by omega : j ≤ r)
      set bj : ℝ := b * Real.exp (2 * γ * j) with hbj
      have hbj0 : 0 < bj := by positivity
      have hbjmax : bj ≤ bmax :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) hb.le
      have hδ0 : 0 ≤ c * j * a ^ j := by positivity
      have hδ1 : c * j * a ^ j ≤ 1 / 4 := by
        have h1 : a ^ j ≤ a ^ r := pow_le_pow_right₀ ha1 (by omega)
        have h2 : c * j ≤ c * r := mul_le_mul_of_nonneg_left hjr hc0.le
        have h3 : c * j * a ^ j ≤ c * r * a ^ r :=
          mul_le_mul h2 h1 (by positivity) (by positivity)
        linarith
      have hβ : 5 * γ * (bj / Fintype.card V) ≤ c / 2 := by
        rw [mul_div_assoc', div_le_iff₀ hnpos]
        have : γ * bj ≤ γ * bmax := mul_le_mul_of_nonneg_left hbjmax hγ0.le
        nlinarith
      obtain ⟨-, ω, -, hgood, -⟩ := hN0 V hN0' s.card (S.reindex s) Bj
        (fun k => Real.exp (2 * γ * j) * w (reidx s k)) bj (c * j * a ^ j) hbj0 hbjmax hδ0 hδ1
        (fun k => hI.alive_sub _ (reidx_mem s k))
        (fun k => mul_nonneg (Real.exp_pos _).le (hw0 _))
        (fun k => by
          calc Real.exp (2 * γ * j) * w (reidx s k)
              ≤ Real.exp (2 * γ * j) * (b / Fintype.card V) :=
                mul_le_mul_of_nonneg_left (hwb _) (Real.exp_pos _).le
            _ = bj / Fintype.card V := by rw [hbj]; ring)
        (fun e he => by
          have h := hI.load e he
          rw [reindex_load S s (fun i => Real.exp (2 * γ * j) * w i) e]
          change |aliveLoad S s (fun i => Real.exp (2 * γ * j) * w i) e - 1| ≤ _ at h
          unfold aliveLoad at h
          exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩)
      exact ⟨_, _, _, _, hI.step hγ0.le (by linarith) (by rw [ha]) hc0.le ω _ hβ hgood⟩
  obtain ⟨s, Bj, W, P, hI⟩ := key r le_rfl
  refine ⟨P, hI.pack, fun v => ?_⟩
  have h1 : (star (B \ edgesOf S P) v).card ≤ (star Bj v).card + (star W v).card :=
    (card_le_card (star_mono hI.cover v)).trans (card_star_union_le _ _ v)
  have h1R : ((star (B \ edgesOf S P) v).card : ℝ) ≤ (star Bj v).card + (star W v).card := by
    exact_mod_cast h1
  have h2 : ((star Bj v).card : ℝ) ≤ η / 2 * Fintype.card V := by
    rcases hI.deg v with h | h
    · exact h.le
    · exact h.trans (mul_le_mul_of_nonneg_right hdeg hnpos.le)
  have h3 : ((star W v).card : ℝ) ≤ η / 4 * Fintype.card V := by
    refine (hI.waste v).trans ?_
    have := mul_le_mul_of_nonneg_right hwaste hnpos.le
    linarith
  nlinarith

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
