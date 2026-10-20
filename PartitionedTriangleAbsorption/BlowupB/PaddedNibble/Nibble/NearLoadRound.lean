/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.Asymptotic

/-! # The near-unit-load physical round (producer)

Parameters `bmax, γ, θ, ε` are fixed first. Then for every sufficiently large
vertex set, every family of distinct physical triangles on an active edge set
`B`, with weights `0 ≤ w ≤ b/n` (`0 < b ≤ bmax`) and edge loads in
`[1-δ, 1+δ]` (`δ ≤ 1/4`), the following holds in the single product space in
which triangle `i` is retained independently with probability `γ w i`:

* the probability that the outcome fails the three round conclusions is `< 1`;
* hence there is an outcome of positive probability satisfying all three at once,
  for which also `B \ E(P) = B' ⊔ W` (exact residual identity).

The packing `P` consists only of retained triangles sharing no edge with another
retained triangle, `Q` is the set of all edges touched by retained triangles,
`B' = B \ Q` and `W = Q \ E(P)`. Nothing in the conclusion is assumed.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/Nibble/NearLoadRound.lean.
Original SHA256: 598fdb51a1564beb3f0363d859a56ad35d94086494c1863fad59b0cd0f286b07.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open BernoulliExposure BernoulliConcentration Finset

theorem cubeWeight_nonneg {n : ℕ} (q : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (ω : Fin n → Bool) : 0 ≤ cubeWeight q ω :=
  prod_nonneg fun i _ => by split_ifs; exacts [(hq i).1, by linarith [(hq i).2]]

/-- A good outcome of positive probability exists when the failure probability is `< 1`. -/
theorem exists_pos_weight_of_cubeProb_lt_one {n : ℕ} (q : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1) (P : (Fin n → Bool) → Prop) (h : cubeProb q P < 1) :
    ∃ ω, 0 < cubeWeight q ω ∧ ¬ P ω := by
  classical
  by_contra hne
  push Not at hne
  have hsum : ∑ ω, cubeWeight q ω = 1 := by
    have := cubeMean_eq_sum_prod q (fun _ => (1 : ℝ))
    rw [cubeMean_const] at this
    simpa using this.symm
  rw [cubeProb_def, cubeMean_eq_sum_prod] at h
  have : ∑ ω, cubeWeight q ω * (if P ω then (1 : ℝ) else 0) = ∑ ω, cubeWeight q ω := by
    apply sum_congr rfl
    intro ω _
    by_cases hP : P ω
    · simp [hP]
    · have h0 : cubeWeight q ω = 0 :=
        le_antisymm (not_lt.mp fun hpos => hP (hne ω hpos)) (cubeWeight_nonneg q hq ω)
      simp [h0]
  linarith

/-- **Near-unit-load physical round.** -/
theorem near_load_round (bmax γ θ ε : ℝ) (hbmax : 0 < bmax) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1 / 128) (hθ : 0 < θ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
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
  obtain ⟨N0, hN0⟩ := eventually_failBound_lt_one bmax γ θ ε hbmax hγ0 (by linarith) hθ hε
  refine ⟨max (max N0 1) (⌈4 * γ * bmax⌉₊), ?_⟩
  intro V _ _ hN m S B w b δ hb hbb hδ0 hδ1 hB hw0 hwb hload
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

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
