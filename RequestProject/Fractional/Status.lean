/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.Local

@[expose] public section

/-!
# Sponsorship status of acute triangles and arithmetic finishing lemmas
-/

namespace NashWilliams.Frac

/-- The three possible sponsorship statuses of an acute triangle with positive edges `pe`, `po`
and negative edge `g`, expressed through normalized demands. -/
lemma acute_status {pe po g : ℝ} (hpe : 0 < pe) (hpo : 0 < po) (hg : g < 0) (hne : pe ≠ po) :
    (po < pe ∧ -g ≤ pe ∧ normT pe g po * pe = -g ∧ normT po g pe = 0) ∨
    (pe < po ∧ -g ≤ po ∧ normT pe g po = 0 ∧ normT po g pe * po = -g) ∨
    (pe < -g ∧ po < -g) := by
  have e1 : normT pe g po = demF pe g po / pe := by
    unfold normT; rw [demF_of_nonneg_f hpo.le]; ring
  have e2 : normT po g pe = demF po g pe / po := by
    unfold normT; rw [demF_of_nonneg_f hpe.le]; ring
  rcases hne.lt_or_gt with hlt | hlt
  · by_cases hs : -g ≤ po
    · right; left
      refine ⟨hlt, hs, ?_, ?_⟩
      · rw [e1, demF_nonsponsor hpe hg hlt hs]; simp
      · rw [e2, demF_sponsor hpo hg hpe.le hlt hs]; field_simp
    · right; right; push_neg at hs; exact ⟨by linarith, hs⟩
  · by_cases hs : -g ≤ pe
    · left
      refine ⟨hlt, hs, ?_, ?_⟩
      · rw [e1, demF_sponsor hpe hg hpo.le hlt hs]; field_simp
      · rw [e2, demF_nonsponsor hpo hg hlt hs]; simp
    · right; right; push_neg at hs; exact ⟨hs, by linarith⟩

/-- The three possible sponsorship statuses, expressed through demands. -/
lemma dem_status {pe po g : ℝ} (hpe : 0 < pe) (hpo : 0 < po) (hg : g < 0) (hne : pe ≠ po) :
    (po < pe ∧ -g ≤ pe ∧ demF pe g po = -g ∧ demF po g pe = 0) ∨
    (pe < po ∧ -g ≤ po ∧ demF pe g po = 0 ∧ demF po g pe = -g) ∨
    (pe < -g ∧ po < -g) := by
  rcases hne.lt_or_gt with hlt | hlt
  · by_cases hs : -g ≤ po
    · right; left
      exact ⟨hlt, hs, demF_nonsponsor hpe hg hlt hs, demF_sponsor hpo hg hpe.le hlt hs⟩
    · right; right; push_neg at hs; exact ⟨by linarith, hs⟩
  · by_cases hs : -g ≤ pe
    · left
      exact ⟨hlt, hs, demF_sponsor hpe hg hpo.le hlt hs, demF_nonsponsor hpo hg hlt hs⟩
    · right; right; push_neg at hs; exact ⟨hs, by linarith⟩

/-- Normalized demand of an obtuse triangle, written in the canonical order. -/
lemma normT_obtuse_le {pe g1 g2 : ℝ} (hc : 0 ≤ pe + g1 + g2) : normT pe g1 g2 ≤ 1 :=
  normT_le_one _ _ _ hc

/-- Finishing lemma with one split of the demand `|φ(f)| = A2 + A3`. -/
lemma fin_gen {F A2 A3 S M2 M3 : ℝ} (hA : A2 + A3 = F) (h2 : 0 ≤ A2) (h3 : 0 ≤ A3)
    (hS2 : A2 = 0 ∨ S + M2 ≤ 4) (hS3 : A3 = 0 ∨ S + M3 ≤ 4) :
    F * S + A2 * M2 + A3 * M3 ≤ 4 * F := by
  have e : F * S + A2 * M2 + A3 * M3 = A2 * (S + M2) + A3 * (S + M3) := by rw [← hA]; ring
  rw [e, ← hA]
  have k2 : A2 * (S + M2) ≤ 4 * A2 := by
    rcases hS2 with h | h
    · rw [h]; simp
    · nlinarith
  have k3 : A3 * (S + M3) ≤ 4 * A3 := by
    rcases hS3 with h | h
    · rw [h]; simp
    · nlinarith
  linarith

/-- Finishing lemma with two independent splits `|φ(f)| = A + A' = B + B'`. -/
lemma fin_gen2 {F A A' B B' P R R' M M' : ℝ} (hF : 0 < F) (hA : A + A' = F) (hB : B + B' = F)
    (h1 : 0 ≤ A) (h2 : 0 ≤ A') (h3 : 0 ≤ B) (h4 : 0 ≤ B')
    (c1 : A = 0 ∨ B = 0 ∨ P + R + M ≤ 4) (c2 : A = 0 ∨ B' = 0 ∨ P + R + M' ≤ 4)
    (c3 : A' = 0 ∨ B = 0 ∨ P + R' + M ≤ 4) (c4 : A' = 0 ∨ B' = 0 ∨ P + R' + M' ≤ 4) :
    F * P + A * R + A' * R' + B * M + B' * M' ≤ 4 * F := by
  have key : ∀ X Y Z : ℝ, 0 ≤ X → 0 ≤ Y → (X = 0 ∨ Y = 0 ∨ Z ≤ 4) → X * Y * Z ≤ 4 * (X * Y) := by
    intro X Y Z hX hY h
    rcases h with h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · exact mul_le_mul_of_nonneg_left h (mul_nonneg hX hY) |>.trans_eq (by ring)
  have k1 := key A B _ h1 h3 c1
  have k2 := key A B' _ h1 h4 c2
  have k3 := key A' B _ h2 h3 c3
  have k4 := key A' B' _ h2 h4 c4
  have e : F * (F * P + A * R + A' * R' + B * M + B' * M') =
      A * B * (P + R + M) + A * B' * (P + R + M') + A' * B * (P + R' + M) +
        A' * B' * (P + R' + M') := by
    rw [← hA] at hB ⊢
    have : B' = A + A' - B := by linarith
    subst this; ring
  have e2 : F * (4 * F) = 4 * (A * B) + 4 * (A * B') + 4 * (A' * B) + 4 * (A' * B') := by
    rw [← hA] at hB ⊢
    have : B' = A + A' - B := by linarith
    subst this; ring
  have : F * (F * P + A * R + A' * R' + B * M + B' * M') ≤ F * (4 * F) := by
    rw [e, e2]; linarith
  exact le_of_mul_le_mul_left this hF

/-- The fraction bound used repeatedly in the case analysis of Lemma 6.1. -/
lemma frac_pair {X Y e e' a b c : ℝ} (hX : X * e = a) (hY : Y * e' = b) (he : c < e)
    (he' : c < e') (hc : a + b ≤ c) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (hc0 : 0 < c) : X + Y ≤ 1 := by
  have : X * c ≤ X * e := mul_le_mul_of_nonneg_left he.le hX0
  have : Y * c ≤ Y * e' := mul_le_mul_of_nonneg_left he'.le hY0
  by_contra hcon
  push_neg at hcon
  nlinarith

end NashWilliams.Frac
