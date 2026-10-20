/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.BipCount

@[expose] public section

/-!
# Lemma 9.5: Claim 9.5.6 by averaging

If `X₁` consists of `u`-obtuse, `X₂` of `v`-obtuse and `X₃, X₄` of acute vertices, then for
every transversal `(z, z', y, y')` with `yy'` a negative edge the four weights between
`{z, z'}` and `{y, y'}` sum to at most `2`.  Averaging over transversals bounds the sum of the
four average weights `m₁₃ + m₂₃ + m₁₄ + m₂₄` by `2` up to an error.
-/

namespace NashWilliams.Frac

open Finset

/-- The four weights of a transversal with `yy'` negative sum to at most `2`. -/
lemma quad_le_two {a1 a2 a3 a4 g1 g2 g3 g4 du dv du' dv' : ℝ}
    (hg1 : 0 ≤ g1) (hg2 : 0 ≤ g2) (hg3 : 0 ≤ g3) (hg4 : 0 ≤ g4)
    (t13 : ¬ (0 < g1 ∧ 0 < g3)) (t24 : ¬ (0 < g2 ∧ 0 < g4))
    (f1 : g1 = 0 → 2 * a1 ≤ dv) (f1' : 2 * a1 ≤ 1 + dv)
    (f2 : g2 = 0 → 2 * a2 ≤ du) (f2' : 2 * a2 ≤ 1 + du)
    (f3 : g3 = 0 → 2 * a3 ≤ dv') (f3' : 2 * a3 ≤ 1 + dv')
    (f4 : g4 = 0 → 2 * a4 ≤ du') (f4' : 2 * a4 ≤ 1 + du')
    (hd : du + dv = 1) (hd' : du' + dv' = 1) :
    a1 + a2 + a3 + a4 ≤ 2 := by
  have z13 : g1 = 0 ∨ g3 = 0 := by
    by_contra h; push_neg at h
    exact t13 ⟨lt_of_le_of_ne hg1 (Ne.symm h.1), lt_of_le_of_ne hg3 (Ne.symm h.2)⟩
  have z24 : g2 = 0 ∨ g4 = 0 := by
    by_contra h; push_neg at h
    exact t24 ⟨lt_of_le_of_ne hg2 (Ne.symm h.1), lt_of_le_of_ne hg4 (Ne.symm h.2)⟩
  rcases z13 with h1 | h3 <;> rcases z24 with h2 | h4
  · linarith [f1 h1, f2 h2]
  · linarith [f1 h1, f4 h4]
  · linarith [f3 h3, f2 h2]
  · linarith [f3 h3, f4 h4]

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- **Claim 9.5.6** (averaged form). -/
theorem claim956 {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop} {du dv : V → ℝ}
    {Su Sv : Finset V} (L : LocFacts C a g U W A du dv Su Sv) {X1 X2 X3 X4 : Finset V}
    (s1 : X1 ⊆ C) (s2 : X2 ⊆ C) (s3 : X3 ⊆ C) (s4 : X4 ⊆ C)
    (t1 : ∀ x ∈ X1, U x) (t2 : ∀ x ∈ X2, W x) (t3 : ∀ x ∈ X3, A x) (t4 : ∀ x ∈ X4, A x)
    {M13 M23 M14 M24 M34 θ B : ℝ} (hθ : 0 ≤ θ) (hM34 : θ < M34)
    (l13 : M13 - θ ≤ 1) (l23 : M23 - θ ≤ 1) (l14 : M14 - θ ≤ 1) (l24 : M24 - θ ≤ 1)
    (b13 : bsum (farI a M13 θ) X1 X3 ≤ B) (b23 : bsum (farI a M23 θ) X2 X3 ≤ B)
    (b14 : bsum (farI a M14 θ) X1 X4 ≤ B) (b24 : bsum (farI a M24 θ) X2 X4 ≤ B)
    (b34 : bsum (farI a M34 θ) X3 X4 ≤ B) {c : ℝ}
    (c1 : (X1.card : ℝ) ≤ c) (c2 : (X2.card : ℝ) ≤ c) (c3 : (X3.card : ℝ) ≤ c)
    (c4 : (X4.card : ℝ) ≤ c) :
    (M13 + M23 + M14 + M24 - 2 - 4 * θ) *
      ((X1.card : ℝ) * X2.card * X3.card * X4.card) ≤ 6 * B * c ^ 2 := by
  have th := L.thin
  set T := trans4 X1 X2 X3 X4
  set n1 : ℝ := (X1.card : ℝ) with hn1
  set n2 : ℝ := (X2.card : ℝ) with hn2
  set n3 : ℝ := (X3.card : ℝ) with hn3
  set n4 : ℝ := (X4.card : ℝ) with hn4
  have n10 : 0 ≤ n1 := Nat.cast_nonneg _
  have n20 : 0 ≤ n2 := Nat.cast_nonneg _
  have n30 : 0 ≤ n3 := Nat.cast_nonneg _
  have n40 : 0 ≤ n4 := Nat.cast_nonneg _
  -- upper bound per transversal
  have hup : ∀ z ∈ T, a z.1.1 z.2.1 + a z.1.2 z.2.1 + a z.1.1 z.2.2 + a z.1.2 z.2.2 ≤
      2 + 2 * farI a M34 θ z.2.1 z.2.2 := by
    intro z hz
    simp only [T, trans4, mem_product] at hz
    obtain ⟨⟨hz1, hz2⟩, hz3, hz4⟩ := hz
    have m1 := s1 hz1; have m2 := s2 hz2; have m3 := s3 hz3; have m4 := s4 hz4
    rcases (L.g0 z.2.1 z.2.2).lt_or_eq with hg | hg
    · have key := quad_le_two (L.g0 z.1.1 z.2.1) (L.g0 z.1.2 z.2.1) (L.g0 z.1.1 z.2.2)
        (L.g0 z.1.2 z.2.2) (fun h => L.tri _ _ _ h.1 h.2 hg)
        (fun h => L.tri _ _ _ h.1 h.2 hg)
        (L.F4u _ m1 _ m3 (t1 _ hz1) (t3 _ hz3)) (L.F5u _ m1 _ m3 (t1 _ hz1) (t3 _ hz3))
        (L.F4w _ m2 _ m3 (t2 _ hz2) (t3 _ hz3)) (L.F5w _ m2 _ m3 (t2 _ hz2) (t3 _ hz3))
        (L.F4u _ m1 _ m4 (t1 _ hz1) (t4 _ hz4)) (L.F5u _ m1 _ m4 (t1 _ hz1) (t4 _ hz4))
        (L.F4w _ m2 _ m4 (t2 _ hz2) (t4 _ hz4)) (L.F5w _ m2 _ m4 (t2 _ hz2) (t4 _ hz4))
        (L.dsum _ m3) (L.dsum _ m4)
      linarith [farI_nonneg a M34 θ z.2.1 z.2.2]
    · have ha0 := L.AA _ m3 _ m4 (t3 _ hz3) (t4 _ hz4) hg.symm
      have hf : 1 ≤ farI a M34 θ z.2.1 z.2.2 := one_le_farI (by
        rw [ha0, zero_sub, abs_neg, abs_of_pos (by linarith)]; exact hM34)
      linarith [th.le_one z.1.1 z.2.1, th.le_one z.1.2 z.2.1, th.le_one z.1.1 z.2.2,
        th.le_one z.1.2 z.2.2]
  have hsum := sum_le_sum hup
  simp only [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hsum
  rw [sum_trans4_xw, sum_trans4_yw, sum_trans4_xt, sum_trans4_yt, sum_trans4_wt] at hsum
  have hTc : ((T.card : ℕ) : ℝ) = n1 * n2 * (n3 * n4) := by
    simp only [T, trans4, card_product]; push_cast; ring
  rw [hTc] at hsum
  -- lower bounds for the block sums
  have e13 := bsum_ge_of_conc th.nonneg l13 X1 X3
  have e23 := bsum_ge_of_conc th.nonneg l23 X2 X3
  have e14 := bsum_ge_of_conc th.nonneg l14 X1 X4
  have e24 := bsum_ge_of_conc th.nonneg l24 X2 X4
  have hc0 : 0 ≤ c := le_trans n10 c1
  have pp : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ c → y ≤ c → x * y ≤ c ^ 2 := by
    intro x y hx hy hxc hyc
    calc x * y ≤ c * c := mul_le_mul hxc hyc hy hc0
      _ = c ^ 2 := by ring
  have qq : ∀ x y : ℝ, ∀ f : V → V → ℝ, (∀ u w, 0 ≤ f u w) → ∀ X Y : Finset V,
      0 ≤ x → 0 ≤ y → x ≤ c → y ≤ c → bsum f X Y ≤ B → x * y * bsum f X Y ≤ c ^ 2 * B :=
    fun x y f hf X Y hx hy hxc hyc hb =>
      mul_le_mul (pp x y hx hy hxc hyc) hb (bsum_nonneg' hf _ _) (sq_nonneg c)
  have q1 := qq n2 n4 _ (farI_nonneg a M13 θ) X1 X3 n20 n40 c2 c4 b13
  have q2 := qq n1 n4 _ (farI_nonneg a M23 θ) X2 X3 n10 n40 c1 c4 b23
  have q3 := qq n2 n3 _ (farI_nonneg a M14 θ) X1 X4 n20 n30 c2 c3 b14
  have q4 := qq n1 n3 _ (farI_nonneg a M24 θ) X2 X4 n10 n30 c1 c3 b24
  have q5 := qq n1 n2 _ (farI_nonneg a M34 θ) X3 X4 n10 n20 c1 c2 b34
  have r13 := mul_le_mul_of_nonneg_left e13 (mul_nonneg n20 n40)
  have r23 := mul_le_mul_of_nonneg_left e23 (mul_nonneg n10 n40)
  have r14 := mul_le_mul_of_nonneg_left e14 (mul_nonneg n20 n30)
  have r24 := mul_le_mul_of_nonneg_left e24 (mul_nonneg n10 n30)
  linarith only [r13, r23, r14, r24, q1, q2, q3, q4, q5, hsum]

end NashWilliams.Frac
