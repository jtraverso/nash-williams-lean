/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.StabConc
public import RequestProject.FracStab.StabW

@[expose] public section

/-!
# Value stability for thin weightings (Lemma 8.10, in the form needed for Lemma 9.5)

`thin_stability`: for every `δ > 0` there are `κ, τ > 0` such that for every `θ > 0` there is
`ε > 0` with the following property.  If `a` is a triangle-thin `K₅`-free `[0,1]`-weighting of a
finite set `S` (`ThinWeights S a`) with `∑_{x,y ∈ S} a x y ≥ (1 - ε)|S|²/2`, then either

* (`CutStruct`) `S` has an almost balanced bipartition such that all but `δ|S|²` of the pairs
  across it have weight at least `1 - δ`, or
* (`QuadStruct`) `S` has a partition into four classes of size at least `κ|S|` with numbers
  `mᵢⱼ ∈ [τ, 1]`, nearly matched (`m₀₁ ≈ m₂₃`, …) with all triangle sums close to `2`, such
  that every bipartition `{i,j} | {k,l}` with `mᵢⱼ ≤ 1 - τ` is almost balanced and all but
  `θ|S|²` of the pairs between classes `i` and `j` have weight within `θ` of `mᵢⱼ`.

These are exactly the outcomes of Lemma 8.10 used in the proof of Lemma 9.5 (the star-cut and
cycle-cut graphons give the first outcome, the reflective-cut and quad-cut graphons the second).
-/

namespace NashWilliams.Frac

open Finset

variable {α : Type*} [DecidableEq α]

/-- First outcome: an almost balanced bipartition with almost all crossing weights near `1`. -/
def CutStruct (S : Finset α) (a : α → α → ℝ) (δ : ℝ) : Prop :=
  ∃ A ⊆ S, (A.card : ℝ) ≤ (1/2 + δ) * S.card ∧ ((S \ A).card : ℝ) ≤ (1/2 + δ) * S.card ∧
    (((A ×ˢ (S \ A)).filter fun p => a p.1 p.2 < 1 - δ).card : ℝ) ≤ δ * (S.card : ℝ) ^ 2

/-- Second outcome: a nearly matched four part structure with concentrated weights. -/
def QuadStruct (S : Finset α) (a : α → α → ℝ) (κ τ θ : ℝ) : Prop :=
  ∃ (V : Fin 4 → Finset α) (m : Fin 4 → Fin 4 → ℝ),
    (∀ i, V i ⊆ S) ∧ (∀ i j, i ≠ j → Disjoint (V i) (V j)) ∧ (∀ x ∈ S, ∃ i, x ∈ V i) ∧
    (∀ i, κ * S.card ≤ (V i).card) ∧ (∀ i j, m i j = m j i) ∧
    (∀ i j, i ≠ j → τ ≤ m i j ∧ m i j ≤ 1) ∧
    (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l → |m i j - m k l| ≤ θ) ∧
    (∀ i j k, i ≠ j → i ≠ k → j ≠ k → |m i j + m i k + m j k - 2| ≤ θ) ∧
    (∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l → m i j ≤ 1 - τ →
      |((V i).card + (V j).card : ℝ) - S.card / 2| ≤ θ * S.card) ∧
    (∀ i j, i ≠ j →
      (((V i ×ˢ V j).filter fun p => θ < |a p.1 p.2 - m i j|).card : ℝ) ≤ θ * (S.card : ℝ) ^ 2)

lemma CutStruct.mono {S : Finset α} {a : α → α → ℝ} {δ δ' : ℝ} (h : CutStruct S a δ)
    (hδ : δ ≤ δ') : CutStruct S a δ' := by
  obtain ⟨A, hA, h1, h2, h3⟩ := h
  have hc : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  refine ⟨A, hA, le_trans h1 (by nlinarith), le_trans h2 (by nlinarith), ?_⟩
  calc _ ≤ ((((A ×ˢ (S \ A)).filter fun p => a p.1 p.2 < 1 - δ).card : ℕ) : ℝ) := by
        exact_mod_cast card_le_card fun p hp => by
          simp only [mem_filter] at hp ⊢; exact ⟨hp.1, by linarith [hp.2]⟩
    _ ≤ δ * (S.card : ℝ) ^ 2 := h3
    _ ≤ δ' * (S.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hδ (sq_nonneg _)

/-! ### Averages over classes -/

omit [DecidableEq α] in
lemma bsum_eq_avgW' (a : α → α → ℝ) (A B : Finset α) :
    bsum a A B = avgW a A B * A.card * B.card := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp [bsum]
  rcases B.eq_empty_or_nonempty with rfl | hB
  · simp [bsum]
  exact bsum_eq_avgW a hA hB

omit [DecidableEq α] in
lemma avgW_comm {a : α → α → ℝ} (hs : ∀ i j, a i j = a j i) (A B : Finset α) :
    avgW a A B = avgW a B A := by
  unfold avgW; rw [bsum_comm hs, mul_comm]

omit [DecidableEq α] in
lemma avgW_nonneg {a : α → α → ℝ} (h0 : ∀ i j, 0 ≤ a i j) (A B : Finset α) :
    0 ≤ avgW a A B := by
  unfold avgW bsum
  exact div_nonneg (sum_nonneg fun _ _ => sum_nonneg fun _ _ => h0 _ _) (by positivity)

omit [DecidableEq α] in
lemma bsum_le_card {a : α → α → ℝ} (h1 : ∀ i j, a i j ≤ 1) (A B : Finset α) :
    bsum a A B ≤ (A.card : ℝ) * B.card := by
  unfold bsum
  calc ∑ x ∈ A, ∑ y ∈ B, a x y ≤ ∑ x ∈ A, ∑ y ∈ B, (1:ℝ) :=
        sum_le_sum fun _ _ => sum_le_sum fun _ _ => h1 _ _
    _ = _ := by simp

omit [DecidableEq α] in
lemma avgW_le_one {a : α → α → ℝ} (h1 : ∀ i j, a i j ≤ 1) (A B : Finset α) :
    avgW a A B ≤ 1 := by
  unfold avgW
  rcases (Nat.cast_nonneg (α := ℝ) (A.card * B.card)).lt_or_eq with h | h
  · push_cast at h; rw [div_le_one h]; exact bsum_le_card h1 A B
  · push_cast at h; rw [← h, div_zero]; exact zero_le_one

omit [DecidableEq α] in
lemma sum_triple (a : α → α → ℝ) (A B C : Finset α) :
    ∑ x ∈ A, ∑ y ∈ B, ∑ w ∈ C, (a x y + a x w + a y w) =
      C.card * bsum a A B + B.card * bsum a A C + A.card * bsum a B C := by
  simp only [sum_add_distrib, sum_const, nsmul_eq_mul, bsum, mul_sum]

omit [DecidableEq α] in
/-- The averaged configuration of three disjoint classes is triangle-thin. -/
lemma avgW_thin {S : Finset α} {a : α → α → ℝ} (H : ThinWeights S a) {A B C : Finset α}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S) (dAB : Disjoint A B) (dAC : Disjoint A C)
    (dBC : Disjoint B C) : avgW a A B + avgW a A C + avgW a B C ≤ 2 := by
  have l := avgW_le_one H.le_one
  have e1 : ∀ B, avgW a ∅ B = 0 := fun B => by simp [avgW]
  have e2 : ∀ B, avgW a B ∅ = 0 := fun B => by simp [avgW]
  rcases A.eq_empty_or_nonempty with rfl | nA
  · rw [e1, e1]; linarith [l B C]
  rcases B.eq_empty_or_nonempty with rfl | nB
  · rw [e1, e2]; linarith [l A C]
  rcases C.eq_empty_or_nonempty with rfl | nC
  · rw [e2, e2]; linarith [l A B]
  have hA0 : (0:ℝ) < A.card := by exact_mod_cast card_pos.2 nA
  have hB0 : (0:ℝ) < B.card := by exact_mod_cast card_pos.2 nB
  have hC0 : (0:ℝ) < C.card := by exact_mod_cast card_pos.2 nC
  have key : ∑ x ∈ A, ∑ y ∈ B, ∑ w ∈ C, (a x y + a x w + a y w) ≤
      ∑ x ∈ A, ∑ y ∈ B, ∑ w ∈ C, (2:ℝ) := by
    refine sum_le_sum fun x hx => sum_le_sum fun y hy => sum_le_sum fun w hw => ?_
    exact H.thin x (hA hx) y (hB hy) w (hC hw) (fun h => disjoint_left.1 dAB hx (h ▸ hy))
      (fun h => disjoint_left.1 dAC hx (h ▸ hw)) (fun h => disjoint_left.1 dBC hy (h ▸ hw))
  rw [sum_triple] at key
  simp only [sum_const, nsmul_eq_mul] at key
  rw [bsum_eq_avgW a nA nB, bsum_eq_avgW a nA nC, bsum_eq_avgW a nB nC] at key
  have hp : (0:ℝ) < A.card * B.card * C.card := by positivity
  nlinarith

end NashWilliams.Frac
