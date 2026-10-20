/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.BipAbs

/-!
# Counting tools for the proof of Lemma 9.5
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Indicator of a far pair: `1` if `|a x y - μ| > θ`, else `0`. -/
noncomputable def farI (a : V → V → ℝ) (μ θ : ℝ) (x y : V) : ℝ :=
  if θ < |a x y - μ| then 1 else 0

omit [DecidableEq V] in
lemma farI_nonneg (a : V → V → ℝ) (μ θ : ℝ) (x y : V) : 0 ≤ farI a μ θ x y := by
  unfold farI; split_ifs <;> norm_num

omit [DecidableEq V] in
lemma farI_le_one (a : V → V → ℝ) (μ θ : ℝ) (x y : V) : farI a μ θ x y ≤ 1 := by
  unfold farI; split_ifs <;> norm_num

omit [DecidableEq V] in
lemma farI_eq_zero {a : V → V → ℝ} {μ θ : ℝ} {x y : V} :
    farI a μ θ x y = 0 ↔ |a x y - μ| ≤ θ := by
  unfold farI; split_ifs with h
  · simp only [one_ne_zero, false_iff, not_le]; exact h
  · simp only [true_iff]; exact not_lt.1 h

omit [DecidableEq V] in
lemma one_le_farI {a : V → V → ℝ} {μ θ : ℝ} {x y : V} (h : θ < |a x y - μ|) :
    1 ≤ farI a μ θ x y := by
  unfold farI; rw [if_pos h]

omit [DecidableEq V] in
lemma farI_symm {a : V → V → ℝ} (hs : ∀ x y, a x y = a y x) (μ θ : ℝ) (x y : V) :
    farI a μ θ x y = farI a μ θ y x := by
  unfold farI; rw [hs]

omit [DecidableEq V] in
lemma bsum_farI (a : V → V → ℝ) (μ θ : ℝ) (X Y : Finset V) :
    bsum (farI a μ θ) X Y = (((X ×ˢ Y).filter fun p => θ < |a p.1 p.2 - μ|).card : ℝ) := by
  unfold bsum farI
  rw [card_filter, sum_product]; push_cast; rfl

omit [DecidableEq V] in
lemma bsum_farI_mono (a : V → V → ℝ) (μ θ : ℝ) {X Y X' Y' : Finset V} (hX : X ⊆ X')
    (hY : Y ⊆ Y') : bsum (farI a μ θ) X Y ≤ bsum (farI a μ θ) X' Y' := by
  rw [bsum_farI, bsum_farI]
  exact_mod_cast card_le_card (filter_subset_filter _ (product_subset_product hX hY))

omit [DecidableEq V] in
lemma bsum_nonneg' {f : V → V → ℝ} (hf : ∀ x y, 0 ≤ f x y) (X Y : Finset V) :
    0 ≤ bsum f X Y :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => hf _ _

omit [DecidableEq V] in
/-- Lower bound for a block sum from concentration. -/
lemma bsum_ge_of_conc {a : V → V → ℝ} (h0 : ∀ x y, 0 ≤ a x y) {μ θ : ℝ} (hμ : μ - θ ≤ 1)
    (X Y : Finset V) :
    (μ - θ) * X.card * Y.card - bsum (farI a μ θ) X Y ≤ bsum a X Y := by
  have key : ∀ x y, μ - θ - farI a μ θ x y ≤ a x y := by
    intro x y
    unfold farI; split_ifs with h
    · linarith [h0 x y]
    · have := (abs_le.1 (not_lt.1 h)).1; linarith
  have : ∑ x ∈ X, ∑ y ∈ Y, (μ - θ - farI a μ θ x y) ≤ bsum a X Y :=
    sum_le_sum fun x _ => sum_le_sum fun y _ => key x y
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul] at this
  rw [show bsum (farI a μ θ) X Y = ∑ x ∈ X, ∑ y ∈ Y, farI a μ θ x y from rfl]
  linarith

omit [DecidableEq V] in
/-- **Triple counting**: if every triple contains a bad pair, there are many bad pairs. -/
lemma triple_count (A1 A2 A3 : Finset V) (f12 f13 f23 : V → V → ℝ)
    (h : ∀ x ∈ A1, ∀ y ∈ A2, ∀ z ∈ A3, 1 ≤ f12 x y + f13 x z + f23 y z) :
    (A1.card : ℝ) * A2.card * A3.card ≤
      A3.card * bsum f12 A1 A2 + A2.card * bsum f13 A1 A3 + A1.card * bsum f23 A2 A3 := by
  have key : ∑ x ∈ A1, ∑ y ∈ A2, ∑ z ∈ A3, (1:ℝ) ≤
      ∑ x ∈ A1, ∑ y ∈ A2, ∑ z ∈ A3, (f12 x y + f13 x z + f23 y z) :=
    sum_le_sum fun x hx => sum_le_sum fun y hy => sum_le_sum fun z hz => h x hx y hy z hz
  have e : ∑ x ∈ A1, ∑ y ∈ A2, ∑ z ∈ A3, (f12 x y + f13 x z + f23 y z) =
      A3.card * bsum f12 A1 A2 + A2.card * bsum f13 A1 A3 + A1.card * bsum f23 A2 A3 := by
    simp only [sum_add_distrib, sum_const, nsmul_eq_mul, bsum, mul_sum]
  rw [e] at key
  simp only [sum_const, nsmul_eq_mul, mul_one] at key
  linarith

omit [DecidableEq V] in
/-- **Bad transversals.** -/
lemma bad4 (A B C D : Finset V) (f1 f2 f3 f4 f5 f6 : V → V → ℝ)
    (hf : ∀ x y, 0 ≤ f1 x y ∧ 0 ≤ f2 x y ∧ 0 ≤ f3 x y ∧ 0 ≤ f4 x y ∧ 0 ≤ f5 x y ∧ 0 ≤ f6 x y)
    (Good : (V × V) × (V × V) → Prop) [DecidablePred Good]
    (hG : ∀ x y w t, ¬ Good ((x, y), (w, t)) →
      1 ≤ f1 x y + f2 x w + f3 x t + f4 y w + f5 y t + f6 w t) :
    (((trans4 A B C D).filter fun z => ¬ Good z).card : ℝ) ≤
      C.card * D.card * bsum f1 A B + B.card * D.card * bsum f2 A C +
      B.card * C.card * bsum f3 A D + A.card * D.card * bsum f4 B C +
      A.card * C.card * bsum f5 B D + A.card * B.card * bsum f6 C D := by
  set F : (V × V) × (V × V) → ℝ := fun z => f1 z.1.1 z.1.2 + f2 z.1.1 z.2.1 + f3 z.1.1 z.2.2 +
    f4 z.1.2 z.2.1 + f5 z.1.2 z.2.2 + f6 z.2.1 z.2.2 with hFdef
  have hF0 : ∀ z, 0 ≤ F z := fun z => by
    obtain ⟨a1, -, -, -, -, -⟩ := hf z.1.1 z.1.2
    obtain ⟨-, a2, -, -, -, -⟩ := hf z.1.1 z.2.1
    obtain ⟨-, -, a3, -, -, -⟩ := hf z.1.1 z.2.2
    obtain ⟨-, -, -, a4, -, -⟩ := hf z.1.2 z.2.1
    obtain ⟨-, -, -, -, a5, -⟩ := hf z.1.2 z.2.2
    obtain ⟨-, -, -, -, -, a6⟩ := hf z.2.1 z.2.2
    simp only [hFdef]; linarith
  calc (((trans4 A B C D).filter fun z => ¬ Good z).card : ℝ)
      = ∑ z ∈ (trans4 A B C D).filter (fun z => ¬ Good z), (1:ℝ) := by
        rw [sum_const, nsmul_eq_mul, mul_one]
    _ ≤ ∑ z ∈ (trans4 A B C D).filter (fun z => ¬ Good z), F z :=
        sum_le_sum fun z hz => hG _ _ _ _ (mem_filter.1 hz).2
    _ ≤ ∑ z ∈ trans4 A B C D, F z :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun z _ _ => hF0 z
    _ = _ := by
        simp only [hFdef, sum_add_distrib]
        rw [sum_trans4_xy, sum_trans4_xw, sum_trans4_xt, sum_trans4_yw, sum_trans4_yt,
          sum_trans4_wt]

omit [DecidableEq V] in
/-- **Poor pairs**: pairs none of whose extensions is good. -/
lemma poor_count (P R : Finset (V × V)) (Good : (V × V) × (V × V) → Prop) [DecidablePred Good] :
    ((P.filter fun p => ∀ r ∈ R, ¬ Good (p, r)).card : ℝ) * R.card ≤
      ((P ×ˢ R).filter fun z => ¬ Good z).card := by
  have hsub : (P.filter fun p => ∀ r ∈ R, ¬ Good (p, r)) ×ˢ R ⊆
      (P ×ˢ R).filter fun z => ¬ Good z := by
    intro z hz
    simp only [mem_product, mem_filter] at hz ⊢
    exact ⟨⟨hz.1.1, hz.2⟩, hz.1.2 z.2 hz.2⟩
  have := card_le_card hsub
  rw [card_product] at this
  exact_mod_cast this

end NashWilliams.Frac
