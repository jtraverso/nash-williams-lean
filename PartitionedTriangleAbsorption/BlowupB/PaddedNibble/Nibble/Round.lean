/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.LoadTail

/-! # One near-unit-load round: the joint failure bound

For a fixed round input we bound the probability, in the single product space
`cubeMean (qv γ w)`, that the outcome fails any of the three conclusions:

1. every star of degree at least `θ n` loses at least `γ d / 8` edges to `P`;
2. every star has waste degree at most `24 γ² n`;
3. every untouched edge has surviving load, rescaled by `e^{2γ}`, within
   `(1+5γ)δ + 5γβ + ε` of one.

The bound `failBound` is an explicit finite sum of exponentials obtained by a
union bound over vertices, link pairs and edges. No independence between the
different events is used.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/Nibble/Round.lean.
Original SHA256: c86f2654e7da289d9722d16a3644e170912627cbda556e3359ca65068e3107f9.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open BernoulliExposure BernoulliConcentration Finset

variable {V : Type*} [DecidableEq V] [Fintype V] {m : ℕ}

/-- The three conclusions of one round, for a single outcome. -/
def RoundGood (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (β δ γ θ ε : ℝ) (ω : Fin m → Bool) : Prop :=
  (∀ v, θ * (Fintype.card V : ℝ) ≤ (star B v).card →
      γ * (star B v).card / 8 ≤ (star (S.packEdges ω) v).card) ∧
  (∀ v, ((star (S.waste ω) v).card : ℝ) ≤ 24 * γ ^ 2 * Fintype.card V) ∧
  (∀ e ∈ S.untouched B ω,
      |Real.exp (2 * γ) * availLoad S B w e ω - 1| ≤ (1 + 5 * γ) * δ + 5 * γ * β + ε)

/-- The explicit failure bound. -/
noncomputable def failBound (n K : ℕ) (β γ θ ε : ℝ) : ℝ :=
  n * (Real.exp (-(γ * (θ * n) / 64)) +
      Real.exp (-(θ * n / (24576 * β * (γ + 1 / 64)))) +
      Real.exp (-(γ * (θ * n) / 128)) +
      Real.exp (-(γ * (θ * n) / (4608 * (K : ℝ) ^ 2 + 96 * K))) +
      Real.exp (-(γ * n / (12 * β))) +
      Real.exp (-(γ ^ 2 * n / 2)) +
      Real.exp (-(γ ^ 3 * n / (2 * (K : ℝ) ^ 2 + 2 * K * γ))) +
      n * Real.exp (-((K : ℝ) / 8))) +
    (n : ℝ) ^ 2 * (2 * Real.exp (-((ε / 2) ^ 2 / (2 * (10 * β * γ + 3 * β * (ε / 2))))))

theorem card_star_le (B : Finset (Sym2 V)) (v : V) : (star B v).card ≤ Fintype.card V := by
  have hsub : star B v ⊆ univ.image (fun a => s(v, a)) := by
    intro e he
    simp only [star, mem_filter] at he
    obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp he.2
    simp
  exact (card_le_card hsub).trans (card_image_le.trans (by simp))

omit [DecidableEq V] in
theorem card_edges_le (B : Finset (Sym2 V)) : B.card ≤ Fintype.card V ^ 2 := by
  classical
  have hsub : B ⊆ (univ ×ˢ univ : Finset (V × V)).image (fun p => Sym2.mk p.1 p.2) := by
    intro e _
    induction e using Sym2.ind with
    | _ a b => exact mem_image.mpr ⟨(a, b), by simp, rfl⟩
  refine (card_le_card hsub).trans (card_image_le.trans ?_)
  simp [sq]

theorem cubeProb_false {n : ℕ} (q : Fin n → ℝ) : cubeProb q (fun _ => False) = 0 := by
  classical
  rw [cubeProb_def]
  simp [cubeMean_const]

open RoundHyp in
/-- Elementary bad events at a vertex. -/
def BadV (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ) (γ θ : ℝ) (K : ℕ)
    (v : V) (ω : Fin m → Bool) : Prop :=
  (θ * (Fintype.card V : ℝ) ≤ (star B v).card ∧
    (((S.retainedThrough ω v).card : ℝ) < γ * (star B v).card / 4 ∨
      (star B v).card / 32 ≤ Yv S w v ω ∨
      (Yv S w v ω ≤ (star B v).card / 32 ∧
        γ * (star B v).card / 16 ≤ (S.blockedRetained ω v).card) ∨
      γ * (star B v).card / 16 ≤ Fhat S v K ω)) ∨
  2 * γ * Fintype.card V ≤ Yv S w v ω ∨
  (Yv S w v ω ≤ 2 * γ * Fintype.card V ∧
    4 * γ ^ 2 * Fintype.card V ≤ (S.blockedRetained ω v).card) ∨
  4 * γ ^ 2 * Fintype.card V ≤ Fhat S v K ω ∨
  ∃ a ∈ univ.erase v, (K : ℝ) ≤ S.linkDeg ω v a

namespace RoundHyp

variable {S : TriSystem V m} {B : Finset (Sym2 V)} {w : Fin m → ℝ} {β δ γ : ℝ}
variable (H : RoundHyp S B w β δ γ)
include H

omit H in
theorem Fhat_eq_conflicts (v : V) (K : ℕ) (ω : Fin m → Bool)
    (h : ∀ a ∈ univ.erase v, ¬ (K : ℝ) ≤ S.linkDeg ω v a) :
    Fhat S v K ω = S.conflicts ω v := by
  unfold Fhat TriSystem.conflicts clip
  push_cast
  apply sum_congr rfl
  intro a ha
  have := h a ha
  push Not at this
  have hlt : S.linkDeg ω v a < K := by exact_mod_cast this
  rw [Nat.min_eq_left hlt.le]

omit H in
/-- Outside the elementary bad events, the progress and waste conclusions hold. -/
theorem good_of_not_bad (θ : ℝ) (K : ℕ) (v : V) (ω : Fin m → Bool) (h : ¬ BadV S B w γ θ K v ω) :
    (θ * (Fintype.card V : ℝ) ≤ (star B v).card →
      γ * (star B v).card / 8 ≤ (star (S.packEdges ω) v).card) ∧
    ((star (S.waste ω) v).card : ℝ) ≤ 24 * γ ^ 2 * Fintype.card V := by
  unfold BadV at h
  push Not at h
  obtain ⟨hprog, hY2, hZ2, hF2, hlink⟩ := h
  have hF := Fhat_eq_conflicts v K ω (fun a ha => by push Not; exact hlink a ha)
  constructor
  · intro hd
    obtain ⟨hR, hY, hZ, hF1⟩ := hprog hd
    have hZ' := hZ hY.le
    have hP := S.progress_inequality ω v
    have hPe := S.card_star_packEdges ω v
    have hPR : ((S.retainedThrough ω v).card : ℝ) ≤
        ((star (S.packEdges ω) v).card / 2 : ℕ) + (S.blockedRetained ω v).card +
          2 * (S.conflicts ω v : ℝ) := by exact_mod_cast hP
    rw [hPe, Nat.mul_div_cancel_left _ (by norm_num)] at hPR
    rw [hPe]
    push_cast
    rw [hF] at hF1
    linarith
  · have hW := S.waste_inequality ω v
    have hW' : ((star (S.waste ω) v).card : ℝ) ≤
        2 * ((S.blockedRetained ω v).card : ℝ) + 4 * (S.conflicts ω v : ℝ) := by
      exact_mod_cast hW
    have hZ := hZ2 hY2.le
    rw [hF] at hF2
    linarith

omit H [DecidableEq V] in
theorem n_pos (v : V) : (0 : ℝ) < Fintype.card V := by
  have : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
  exact_mod_cast this

omit H in
theorem d_le_n (v : V) : ((star B v).card : ℝ) ≤ Fintype.card V := by
  exact_mod_cast card_star_le B v

/-- The progress block of the bad events at one vertex. -/
theorem prog_prob_le (θ : ℝ) (hθ : 0 < θ) (K : ℕ) (hK : 1 ≤ K) (v : V) :
    cubeProb (qv γ w) (fun ω => θ * (Fintype.card V : ℝ) ≤ (star B v).card ∧
      (((S.retainedThrough ω v).card : ℝ) < γ * (star B v).card / 4 ∨
        (star B v).card / 32 ≤ Yv S w v ω ∨
        (Yv S w v ω ≤ (star B v).card / 32 ∧
          γ * (star B v).card / 16 ≤ (S.blockedRetained ω v).card) ∨
        γ * (star B v).card / 16 ≤ Fhat S v K ω)) ≤
      Real.exp (-(γ * (θ * Fintype.card V) / 64)) +
      Real.exp (-(θ * Fintype.card V / (24576 * β * (γ + 1 / 64)))) +
      Real.exp (-(γ * (θ * Fintype.card V) / 128)) +
      Real.exp (-(γ * (θ * Fintype.card V) / (4608 * (K : ℝ) ^ 2 + 96 * K))) := by
  have hq := H.hq
  have hn := n_pos (V := V) v
  have hγ := H.γ0; have hγ1 := H.γ1; have hβ := H.β0
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  by_cases hdθ : θ * (Fintype.card V : ℝ) ≤ (star B v).card
  · have hdpos : (0 : ℝ) < (star B v).card := lt_of_lt_of_le (mul_pos hθ hn) hdθ
    have hdnat : 0 < (star B v).card := by exact_mod_cast hdpos
    obtain ⟨d, hd⟩ : ∃ d : ℝ, ((star B v).card : ℝ) = d := ⟨_, rfl⟩
    obtain ⟨n, hnd⟩ : ∃ n : ℝ, (Fintype.card V : ℝ) = n := ⟨_, rfl⟩
    rw [hd, hnd] at hdθ
    rw [hd] at hdpos
    rw [hnd] at hn
    have e1 := H.R_tail v hdnat
    rw [hd] at e1
    have e2 := H.Y_tail v (d / 32) (d / 64) (by positivity) (by rw [hd]; nlinarith)
    rw [hd] at e2
    have e3 := H.Z_tail v (d / 32) (γ * d / 16)
    have hγd : γ ^ 2 * d ≤ γ * d / 48 := by
      have := mul_le_mul_of_nonneg_right hγ1 (mul_nonneg hγ.le hdpos.le)
      nlinarith
    have e4 := H.Fhat_tail v K hK (γ * d / 16) (γ * d / 24) (by positivity)
      (by rw [hd]; linarith)
    rw [hd] at e4
    have b1 : Real.exp (-(γ * d / 64)) ≤ Real.exp (-(γ * (θ * n) / 64)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have b2 : Real.exp (-((d / 64) ^ 2 / (2 * (3 * β * (γ * d) + 3 * β * (d / 64))))) ≤
        Real.exp (-(θ * n / (24576 * β * (γ + 1 / 64)))) := by
      apply Real.exp_le_exp.mpr
      have : (d / 64) ^ 2 / (2 * (3 * β * (γ * d) + 3 * β * (d / 64))) =
          d / (24576 * β * (γ + 1 / 64)) := by field_simp; ring
      rw [this, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right hdθ (by positivity)
    have b3 : Real.exp (-(γ * d / 16 / 2) + 3 / 4 * (γ * (d / 32))) ≤
        Real.exp (-(γ * (θ * n) / 128)) := by
      apply Real.exp_le_exp.mpr; nlinarith
    have b4 : Real.exp (-((γ * d / 24) ^ 2 / (2 * (4 * (K : ℝ) ^ 2 * (γ * d) +
        2 * (K : ℝ) * (γ * d / 24))))) ≤
        Real.exp (-(γ * (θ * n) / (4608 * (K : ℝ) ^ 2 + 96 * K))) := by
      apply Real.exp_le_exp.mpr
      have : (γ * d / 24) ^ 2 / (2 * (4 * (K : ℝ) ^ 2 * (γ * d) + 2 * (K : ℝ) * (γ * d / 24))) =
          γ * d / (4608 * (K : ℝ) ^ 2 + 96 * K) := by field_simp; ring
      rw [this, neg_le_neg_iff]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    rw [hd, hnd]
    have o1 := cubeProb_or_le (qv γ w) hq
      (fun ω => Yv S w v ω ≤ d / 32 ∧ γ * d / 16 ≤ (S.blockedRetained ω v).card)
      (fun ω => γ * d / 16 ≤ Fhat S v K ω)
    have o2 := cubeProb_or_le (qv γ w) hq (fun ω => d / 32 ≤ Yv S w v ω)
      (fun ω => (Yv S w v ω ≤ d / 32 ∧ γ * d / 16 ≤ (S.blockedRetained ω v).card) ∨
        γ * d / 16 ≤ Fhat S v K ω)
    have o3 := cubeProb_or_le (qv γ w) hq
      (fun ω => ((S.retainedThrough ω v).card : ℝ) < γ * d / 4)
      (fun ω => d / 32 ≤ Yv S w v ω ∨
        (Yv S w v ω ≤ d / 32 ∧ γ * d / 16 ≤ (S.blockedRetained ω v).card) ∨
        γ * d / 16 ≤ Fhat S v K ω)
    have m0 := cubeProb_mono (qv γ w) hq (P := fun ω => θ * n ≤ d ∧
      (((S.retainedThrough ω v).card : ℝ) < γ * d / 4 ∨ d / 32 ≤ Yv S w v ω ∨
        (Yv S w v ω ≤ d / 32 ∧ γ * d / 16 ≤ (S.blockedRetained ω v).card) ∨
        γ * d / 16 ≤ Fhat S v K ω)) (fun ω h => h.2)
    linarith [e1.trans b1, e2.trans b2, e3.trans b3, e4.trans b4]
  · calc _ ≤ cubeProb (qv γ w) (fun _ => False) :=
          cubeProb_mono _ hq (fun ω h => hdθ h.1)
      _ = 0 := cubeProb_false _
      _ ≤ _ := by positivity

/-- The waste and link blocks of the bad events at one vertex. -/
theorem waste_prob_le (K : ℕ) (hK : 1 ≤ K) (v : V) :
    cubeProb (qv γ w) (fun ω => 2 * γ * Fintype.card V ≤ Yv S w v ω ∨
      (Yv S w v ω ≤ 2 * γ * Fintype.card V ∧
        4 * γ ^ 2 * Fintype.card V ≤ (S.blockedRetained ω v).card) ∨
      4 * γ ^ 2 * Fintype.card V ≤ Fhat S v K ω ∨
      ∃ a ∈ univ.erase v, (K : ℝ) ≤ S.linkDeg ω v a) ≤
      Real.exp (-(γ * Fintype.card V / (12 * β))) +
      Real.exp (-(γ ^ 2 * Fintype.card V / 2)) +
      Real.exp (-(γ ^ 3 * Fintype.card V / (2 * (K : ℝ) ^ 2 + 2 * K * γ))) +
      Fintype.card V * Real.exp (-((K : ℝ) / 8)) := by
  have hq := H.hq
  have hn := n_pos (V := V) v
  have hdn := d_le_n (B := B) v
  have hγ := H.γ0; have hβ := H.β0
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  obtain ⟨d, hd⟩ : ∃ d : ℝ, ((star B v).card : ℝ) = d := ⟨_, rfl⟩
  obtain ⟨n, hnd⟩ : ∃ n : ℝ, (Fintype.card V : ℝ) = n := ⟨_, rfl⟩
  rw [hd, hnd] at hdn
  rw [hnd] at hn
  have hd0 : 0 ≤ d := by rw [← hd]; exact Nat.cast_nonneg _
  have e5 := H.Y_tail v (2 * γ * n) (γ * n) (by positivity) (by rw [hd]; nlinarith)
  rw [hd] at e5
  have b5 : Real.exp (-((γ * n) ^ 2 / (2 * (3 * β * (γ * d) + 3 * β * (γ * n))))) ≤
      Real.exp (-(γ * n / (12 * β))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    have : γ * n / (12 * β) = (γ * n) ^ 2 / (2 * (3 * β * (γ * n) + 3 * β * (γ * n))) := by
      field_simp; ring
    rw [this]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left hdn (by positivity : (0 : ℝ) ≤ 3 * β * γ)
    nlinarith
  have e6 := H.Z_tail v (2 * γ * n) (4 * γ ^ 2 * n)
  have b6 : Real.exp (-(4 * γ ^ 2 * n / 2) + 3 / 4 * (γ * (2 * γ * n))) ≤
      Real.exp (-(γ ^ 2 * n / 2)) := by
    apply Real.exp_le_exp.mpr; nlinarith
  have e7 := H.Fhat_tail v K hK (4 * γ ^ 2 * n) (2 * γ ^ 2 * n) (by positivity)
    (by rw [hd]; nlinarith [mul_le_mul_of_nonneg_left hdn (sq_nonneg γ)])
  rw [hd] at e7
  have b7 : Real.exp (-((2 * γ ^ 2 * n) ^ 2 / (2 * (4 * (K : ℝ) ^ 2 * (γ * d) +
      2 * (K : ℝ) * (2 * γ ^ 2 * n))))) ≤
      Real.exp (-(γ ^ 3 * n / (2 * (K : ℝ) ^ 2 + 2 * K * γ))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    have : γ ^ 3 * n / (2 * (K : ℝ) ^ 2 + 2 * K * γ) =
        (2 * γ ^ 2 * n) ^ 2 /
          (2 * (4 * (K : ℝ) ^ 2 * (γ * n) + 2 * (K : ℝ) * (2 * γ ^ 2 * n))) := by
      field_simp; ring
    rw [this]
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have := mul_le_mul_of_nonneg_left hdn (by positivity : (0 : ℝ) ≤ 4 * (K : ℝ) ^ 2 * γ)
    nlinarith
  have e8 : cubeProb (qv γ w) (fun ω => ∃ a ∈ univ.erase v, (K : ℝ) ≤ S.linkDeg ω v a) ≤
      n * Real.exp (-((K : ℝ) / 8)) := by
    refine (cubeProb_exists_le _ hq _ _).trans ?_
    calc _ ≤ ∑ _a ∈ univ.erase v, Real.exp (-((K : ℝ) / 8)) :=
          sum_le_sum fun a ha => H.linkDeg_tail v a (mem_erase.mp ha).1 K hK
      _ = ((univ.erase v).card : ℝ) * Real.exp (-((K : ℝ) / 8)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ n * Real.exp (-((K : ℝ) / 8)) := by
          apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
          rw [← hnd]; exact_mod_cast (card_erase_le.trans (by simp))
  rw [hnd]
  have o1 := cubeProb_or_le (qv γ w) hq (fun ω => 4 * γ ^ 2 * n ≤ Fhat S v K ω)
    (fun ω => ∃ a ∈ univ.erase v, (K : ℝ) ≤ S.linkDeg ω v a)
  have o2 := cubeProb_or_le (qv γ w) hq
    (fun ω => Yv S w v ω ≤ 2 * γ * n ∧ 4 * γ ^ 2 * n ≤ (S.blockedRetained ω v).card)
    (fun ω => 4 * γ ^ 2 * n ≤ Fhat S v K ω ∨ ∃ a ∈ univ.erase v, (K : ℝ) ≤ S.linkDeg ω v a)
  have o3 := cubeProb_or_le (qv γ w) hq (fun ω => 2 * γ * n ≤ Yv S w v ω)
    (fun ω => (Yv S w v ω ≤ 2 * γ * n ∧ 4 * γ ^ 2 * n ≤ (S.blockedRetained ω v).card) ∨
      4 * γ ^ 2 * n ≤ Fhat S v K ω ∨ ∃ a ∈ univ.erase v, (K : ℝ) ≤ S.linkDeg ω v a)
  linarith [e5.trans b5, e6.trans b6, e7.trans b7]

/-- The probability of the elementary bad events at one vertex. -/
theorem badV_prob_le (θ : ℝ) (hθ : 0 < θ) (K : ℕ) (hK : 1 ≤ K) (v : V) :
    cubeProb (qv γ w) (BadV S B w γ θ K v) ≤
      Real.exp (-(γ * (θ * Fintype.card V) / 64)) +
      Real.exp (-(θ * Fintype.card V / (24576 * β * (γ + 1 / 64)))) +
      Real.exp (-(γ * (θ * Fintype.card V) / 128)) +
      Real.exp (-(γ * (θ * Fintype.card V) / (4608 * (K : ℝ) ^ 2 + 96 * K))) +
      Real.exp (-(γ * Fintype.card V / (12 * β))) +
      Real.exp (-(γ ^ 2 * Fintype.card V / 2)) +
      Real.exp (-(γ ^ 3 * Fintype.card V / (2 * (K : ℝ) ^ 2 + 2 * K * γ))) +
      Fintype.card V * Real.exp (-((K : ℝ) / 8)) := by
  have h := cubeProb_or_le (qv γ w) H.hq _ _ |>.trans
    (add_le_add (H.prog_prob_le θ hθ K hK v) (H.waste_prob_le K hK v))
  unfold BadV
  linarith

/-- The joint failure probability of one round. -/
theorem round_fail_le (θ ε : ℝ) (hθ : 0 < θ) (hε : 0 < ε) (K : ℕ) (hK : 1 ≤ K) :
    cubeProb (qv γ w) (fun ω => ¬ RoundGood S B w β δ γ θ ε ω) ≤
      failBound (Fintype.card V) K β γ θ ε := by
  classical
  have hq := H.hq
  have hsub : ∀ ω, ¬ RoundGood S B w β δ γ θ ε ω →
      (∃ v ∈ (univ : Finset V), BadV S B w γ θ K v ω) ∨
      (∃ e ∈ B, e ∈ S.untouched B ω ∧
        (1 + 5 * γ) * δ + 5 * γ * β + ε < |Real.exp (2 * γ) * availLoad S B w e ω - 1|) := by
    intro ω hbad
    by_contra hcon
    push Not at hcon
    obtain ⟨hv, he⟩ := hcon
    apply hbad
    refine ⟨fun v hd => (good_of_not_bad θ K v ω (hv v (mem_univ v))).1 hd,
      fun v => (good_of_not_bad θ K v ω (hv v (mem_univ v))).2, fun e heU => ?_⟩
    have heB : e ∈ B := ((mem_untouched_iff S B e ω).mp heU).1
    exact he e heB heU
  refine (cubeProb_mono _ hq hsub).trans ((cubeProb_or_le _ hq _ _).trans ?_)
  have hV := cubeProb_exists_le (qv γ w) hq (univ : Finset V) (BadV S B w γ θ K)
  have hE := cubeProb_exists_le (qv γ w) hq B (fun e ω => e ∈ S.untouched B ω ∧
    (1 + 5 * γ) * δ + 5 * γ * β + ε < |Real.exp (2 * γ) * availLoad S B w e ω - 1|)
  have hV' : ∑ v ∈ (univ : Finset V), cubeProb (qv γ w) (BadV S B w γ θ K v) ≤
      (Fintype.card V : ℝ) * (Real.exp (-(γ * (θ * Fintype.card V) / 64)) +
      Real.exp (-(θ * Fintype.card V / (24576 * β * (γ + 1 / 64)))) +
      Real.exp (-(γ * (θ * Fintype.card V) / 128)) +
      Real.exp (-(γ * (θ * Fintype.card V) / (4608 * (K : ℝ) ^ 2 + 96 * K))) +
      Real.exp (-(γ * Fintype.card V / (12 * β))) +
      Real.exp (-(γ ^ 2 * Fintype.card V / 2)) +
      Real.exp (-(γ ^ 3 * Fintype.card V / (2 * (K : ℝ) ^ 2 + 2 * K * γ))) +
      Fintype.card V * Real.exp (-((K : ℝ) / 8))) := by
    calc _ ≤ ∑ _v ∈ (univ : Finset V), (Real.exp (-(γ * (θ * Fintype.card V) / 64)) +
      Real.exp (-(θ * Fintype.card V / (24576 * β * (γ + 1 / 64)))) +
      Real.exp (-(γ * (θ * Fintype.card V) / 128)) +
      Real.exp (-(γ * (θ * Fintype.card V) / (4608 * (K : ℝ) ^ 2 + 96 * K))) +
      Real.exp (-(γ * Fintype.card V / (12 * β))) +
      Real.exp (-(γ ^ 2 * Fintype.card V / 2)) +
      Real.exp (-(γ ^ 3 * Fintype.card V / (2 * (K : ℝ) ^ 2 + 2 * K * γ))) +
      Fintype.card V * Real.exp (-((K : ℝ) / 8))) :=
          sum_le_sum fun v _ => H.badV_prob_le θ hθ K hK v
      _ = _ := by rw [sum_const, nsmul_eq_mul, card_univ]
  have hE' : ∑ e ∈ B, cubeProb (qv γ w) (fun ω => e ∈ S.untouched B ω ∧
      (1 + 5 * γ) * δ + 5 * γ * β + ε < |Real.exp (2 * γ) * availLoad S B w e ω - 1|) ≤
      (Fintype.card V : ℝ) ^ 2 *
        (2 * Real.exp (-((ε / 2) ^ 2 / (2 * (10 * β * γ + 3 * β * (ε / 2)))))) := by
    calc _ ≤ ∑ _e ∈ B, 2 * Real.exp (-((ε / 2) ^ 2 / (2 * (10 * β * γ + 3 * β * (ε / 2))))) :=
          sum_le_sum fun e _ => H.load_tail e ε hε
      _ = (B.card : ℝ) *
          (2 * Real.exp (-((ε / 2) ^ 2 / (2 * (10 * β * γ + 3 * β * (ε / 2)))))) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast card_edges_le B
  unfold failBound
  linarith

end RoundHyp

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
