/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.StabGreedy

@[expose] public section

/-!
# Concentration of pair weights via random transversals (proof of Lemma 8.10)

Let `A, B, C, D` be four disjoint classes of a triangle-thin weighting.  For a transversal
`z = (x, y, w, t) ∈ A × B × C × D` the four triangle sums of `z` are at most `2`, hence
`|a(x,y) - a(w,t)| ≤ 4 - (sum of the six pair weights of z)`.  If the averaged configuration is
nearly matched (its six average weights sum to almost `4`), Markov's inequality shows that
`a(x,y)` and `a(w,t)` almost always agree; since the two pairs are independent coordinates, the
weight `a(x,y)` is then concentrated around its average over `A × B` (`conc_of_split`).
-/

namespace NashWilliams.Frac

open Finset

variable {α : Type*} [DecidableEq α]

/-- Markov's inequality for a finite sum. -/
lemma card_filter_mul_le {β : Type*} (s : Finset β) (f : β → ℝ) (hf : ∀ x ∈ s, 0 ≤ f x)
    (t : ℝ) : ((s.filter fun x => t < f x).card : ℝ) * t ≤ ∑ x ∈ s, f x := by
  calc ((s.filter fun x => t < f x).card : ℝ) * t = ∑ x ∈ s.filter (fun x => t < f x), t := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ s.filter (fun x => t < f x), f x :=
        sum_le_sum fun x hx => (mem_filter.1 hx).2.le
    _ ≤ ∑ x ∈ s, f x := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        fun x hx _ => hf x hx

/-- **Concentration from agreement with an independent copy.** -/
lemma conc_of_split {β γ : Type*} (P : Finset β) (R : Finset γ) (g : β → ℝ) (h : γ → ℝ)
    (hg0 : ∀ p, 0 ≤ g p) (hg1 : ∀ p, g p ≤ 1) (hh0 : ∀ r, 0 ≤ h r) (hh1 : ∀ r, h r ≤ 1)
    {r0 p0 : ℝ} (hr0 : 0 ≤ r0) (hR : R.Nonempty)
    (hbad : (((P ×ˢ R).filter fun z => r0 < |g z.1 - h z.2|).card : ℝ) ≤ p0 * P.card * R.card) :
    ((P.filter fun p => 2 * r0 + p0 < |g p - (∑ q ∈ P, g q) / P.card|).card : ℝ) ≤
      p0 * P.card := by
  classical
  rcases P.eq_empty_or_nonempty with rfl | hP
  · simp
  have hPc : (0:ℝ) < P.card := by exact_mod_cast card_pos.2 hP
  -- a good `r`
  have hsum : ∑ r ∈ R, ((P.filter fun p => r0 < |g p - h r|).card : ℝ) ≤
      ∑ r ∈ R, p0 * P.card := by
    rw [sum_const, nsmul_eq_mul]
    have hn : ((P ×ˢ R).filter fun z => r0 < |g z.1 - h z.2|).card =
        ∑ r ∈ R, (P.filter fun p => r0 < |g p - h r|).card := by
      rw [card_filter, sum_product_right]
      exact sum_congr rfl fun r _ => (card_filter _ _).symm
    have : ∑ r ∈ R, ((P.filter fun p => r0 < |g p - h r|).card : ℝ) =
        (((P ×ˢ R).filter fun z => r0 < |g z.1 - h z.2|).card : ℝ) := by
      rw [hn]; push_cast; rfl
    rw [this]; linarith
  obtain ⟨r, -, hr⟩ := exists_le_of_sum_le hR hsum
  set b := h r
  set Bd := P.filter fun p => r0 < |g p - b|
  -- the average is close to `b`
  have havg : |(∑ q ∈ P, g q) / P.card - b| ≤ r0 + p0 := by
    have e : (∑ q ∈ P, g q) / P.card - b = (∑ q ∈ P, (g q - b)) / P.card := by
      rw [sum_sub_distrib, sum_const, nsmul_eq_mul]; field_simp
    rw [e, abs_div, abs_of_pos hPc, div_le_iff₀ hPc]
    rw [← sum_filter_add_sum_filter_not P (fun p => r0 < |g p - b|)]
    have h1 : |∑ q ∈ P with r0 < |g q - b|, (g q - b)| ≤ p0 * P.card := by
      calc _ ≤ ∑ q ∈ P with r0 < |g q - b|, |g q - b| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ P with r0 < |g q - b|, (1:ℝ) := sum_le_sum fun q _ =>
            abs_le.2 ⟨by linarith [hg0 q, hh1 r], by linarith [hg1 q, hh0 r]⟩
        _ = Bd.card := by rw [sum_const, nsmul_eq_mul, mul_one]
        _ ≤ p0 * P.card := hr
    have h2 : |∑ q ∈ P with ¬ r0 < |g q - b|, (g q - b)| ≤ r0 * P.card := by
      calc _ ≤ ∑ q ∈ P with ¬ r0 < |g q - b|, |g q - b| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ q ∈ P with ¬ r0 < |g q - b|, r0 := sum_le_sum fun q hq =>
            not_lt.1 (mem_filter.1 hq).2
        _ = (P.filter fun q => ¬ r0 < |g q - b|).card * r0 := by rw [sum_const, nsmul_eq_mul]
        _ ≤ P.card * r0 := mul_le_mul_of_nonneg_right
            (by exact_mod_cast card_filter_le _ _) hr0
        _ = r0 * P.card := by ring
    calc _ ≤ |∑ q ∈ P with r0 < |g q - b|, (g q - b)| +
          |∑ q ∈ P with ¬ r0 < |g q - b|, (g q - b)| := abs_add_le _ _
      _ ≤ (r0 + p0) * P.card := by linarith
  -- far from the average implies far from `b`
  have hsub : (P.filter fun p => 2 * r0 + p0 < |g p - (∑ q ∈ P, g q) / P.card|) ⊆ Bd := by
    intro p hp
    rw [mem_filter] at hp ⊢
    refine ⟨hp.1, ?_⟩
    have := abs_sub_abs_le_abs_sub (g p - (∑ q ∈ P, g q) / P.card)
      ((∑ q ∈ P, g q) / P.card - b)
    have e : g p - (∑ q ∈ P, g q) / ↑P.card - ((∑ q ∈ P, g q) / ↑P.card - b) =
        g p - b + 2 * (b - (∑ q ∈ P, g q) / P.card) := by ring
    have h3 : |g p - b| ≥ |g p - (∑ q ∈ P, g q) / P.card| -
        |(∑ q ∈ P, g q) / P.card - b| := by
      have := abs_sub_abs_le_abs_sub (g p - b) ((∑ q ∈ P, g q) / P.card - b)
      have e2 : g p - b - ((∑ q ∈ P, g q) / ↑P.card - b) = g p - (∑ q ∈ P, g q) / P.card := by
        ring
      rw [e2] at this
      have := abs_sub_abs_le_abs_sub (g p - (∑ q ∈ P, g q) / P.card)
        (b - (∑ q ∈ P, g q) / P.card)
      have e3 : g p - (∑ q ∈ P, g q) / ↑P.card - (b - (∑ q ∈ P, g q) / ↑P.card) = g p - b := by
        ring
      rw [e3, abs_sub_comm b] at this
      linarith
    linarith [hp.2]
  calc _ ≤ (Bd.card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ p0 * P.card := hr

/-! ### Sums over transversals -/

section transversal

variable (A B C D : Finset α) (f : α → α → ℝ)

/-- Transversals of four classes. -/
abbrev trans4 : Finset ((α × α) × (α × α)) := (A ×ˢ B) ×ˢ (C ×ˢ D)

omit [DecidableEq α] in
lemma sum_trans4 (F : (α × α) × (α × α) → ℝ) :
    ∑ z ∈ trans4 A B C D, F z = ∑ x ∈ A, ∑ y ∈ B, ∑ w ∈ C, ∑ t ∈ D, F ((x, y), (w, t)) := by
  simp only [trans4, sum_product]

omit [DecidableEq α] in
lemma sum_trans4_xy : ∑ z ∈ trans4 A B C D, f z.1.1 z.1.2 = C.card * D.card * bsum f A B := by
  rw [sum_trans4]; simp only [sum_const, nsmul_eq_mul, bsum, mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  ring

omit [DecidableEq α] in
lemma sum_trans4_xw : ∑ z ∈ trans4 A B C D, f z.1.1 z.2.1 = B.card * D.card * bsum f A C := by
  rw [sum_trans4]; simp only [sum_const, nsmul_eq_mul, bsum, mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  ring_nf

omit [DecidableEq α] in
lemma sum_trans4_xt : ∑ z ∈ trans4 A B C D, f z.1.1 z.2.2 = B.card * C.card * bsum f A D := by
  rw [sum_trans4]; simp only [sum_const, nsmul_eq_mul, bsum, mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  ring_nf

omit [DecidableEq α] in
lemma sum_trans4_yw : ∑ z ∈ trans4 A B C D, f z.1.2 z.2.1 = A.card * D.card * bsum f B C := by
  rw [sum_trans4]; simp only [sum_const, nsmul_eq_mul, bsum, mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  ring_nf

omit [DecidableEq α] in
lemma sum_trans4_yt : ∑ z ∈ trans4 A B C D, f z.1.2 z.2.2 = A.card * C.card * bsum f B D := by
  rw [sum_trans4]; simp only [sum_const, nsmul_eq_mul, bsum, mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  ring_nf

omit [DecidableEq α] in
lemma sum_trans4_wt : ∑ z ∈ trans4 A B C D, f z.2.1 z.2.2 = A.card * B.card * bsum f C D := by
  rw [sum_trans4]; simp only [sum_const, nsmul_eq_mul, bsum, mul_sum]
  refine sum_congr rfl fun _ _ => ?_
  ring_nf

end transversal

/-- Average weight between two classes. -/
noncomputable def avgW (a : α → α → ℝ) (A B : Finset α) : ℝ :=
  bsum a A B / ((A.card : ℝ) * B.card)

omit [DecidableEq α] in
lemma bsum_eq_avgW (a : α → α → ℝ) {A B : Finset α} (hA : A.Nonempty) (hB : B.Nonempty) :
    bsum a A B = avgW a A B * A.card * B.card := by
  have h1 : (0:ℝ) < A.card := by exact_mod_cast card_pos.2 hA
  have h2 : (0:ℝ) < B.card := by exact_mod_cast card_pos.2 hB
  unfold avgW; field_simp

omit [DecidableEq α] in
/-- **Concentration of the weights between two classes** (the heart of Lemma 8.10).  If the
six average weights of four disjoint nonempty classes sum to at least `4 - e`, then all but an
`e/r₀` fraction of the pairs of `A × B` have weight within `2 r₀ + e / r₀` of the average. -/
lemma conc_pair {S : Finset α} {a : α → α → ℝ} (H : ThinWeights S a) {A B C D : Finset α}
    (hA : A ⊆ S) (hB : B ⊆ S) (hC : C ⊆ S) (hD : D ⊆ S)
    (dAB : Disjoint A B) (dAC : Disjoint A C) (dAD : Disjoint A D) (dBC : Disjoint B C)
    (dBD : Disjoint B D) (dCD : Disjoint C D)
    (nA : A.Nonempty) (nB : B.Nonempty) (nC : C.Nonempty) (nD : D.Nonempty)
    {e r0 : ℝ} (hr0 : 0 < r0)
    (hslack : 4 - (avgW a A B + avgW a A C + avgW a A D + avgW a B C + avgW a B D +
      avgW a C D) ≤ e) :
    (((A ×ˢ B).filter fun p => 2 * r0 + e / r0 < |a p.1 p.2 - avgW a A B|).card : ℝ) ≤
      e / r0 * A.card * B.card := by
  classical
  set G : (α × α) × (α × α) → ℝ := fun z => 4 - (a z.1.1 z.1.2 + a z.1.1 z.2.1 + a z.1.1 z.2.2 +
    a z.1.2 z.2.1 + a z.1.2 z.2.2 + a z.2.1 z.2.2)
  -- pointwise facts on transversals
  have hz : ∀ z ∈ trans4 A B C D, 0 ≤ G z ∧ |a z.1.1 z.1.2 - a z.2.1 z.2.2| ≤ G z := by
    rintro ⟨⟨x, y⟩, ⟨w, t⟩⟩ hzT
    simp only [trans4, mem_product] at hzT
    obtain ⟨⟨hx, hy⟩, hw, ht⟩ := hzT
    have nxy : x ≠ y := fun h => disjoint_left.1 dAB hx (h ▸ hy)
    have nxw : x ≠ w := fun h => disjoint_left.1 dAC hx (h ▸ hw)
    have nxt : x ≠ t := fun h => disjoint_left.1 dAD hx (h ▸ ht)
    have nyw : y ≠ w := fun h => disjoint_left.1 dBC hy (h ▸ hw)
    have nyt : y ≠ t := fun h => disjoint_left.1 dBD hy (h ▸ ht)
    have nwt : w ≠ t := fun h => disjoint_left.1 dCD hw (h ▸ ht)
    have t1 := H.thin x (hA hx) y (hB hy) w (hC hw) nxy nxw nyw
    have t2 := H.thin x (hA hx) y (hB hy) t (hD ht) nxy nxt nyt
    have t3 := H.thin x (hA hx) w (hC hw) t (hD ht) nxw nxt nwt
    have t4 := H.thin y (hB hy) w (hC hw) t (hD ht) nyw nyt nwt
    simp only [G]
    refine ⟨by linarith, abs_le.2 ⟨by linarith, by linarith⟩⟩
  -- the sum of `G` over all transversals
  have hcard : ∀ {X Y : Finset α}, X.Nonempty → Y.Nonempty → bsum a X Y =
      avgW a X Y * X.card * Y.card := fun hX hY => bsum_eq_avgW a hX hY
  have hsumG : ∑ z ∈ trans4 A B C D, G z = (A.card : ℝ) * B.card * C.card * D.card *
      (4 - (avgW a A B + avgW a A C + avgW a A D + avgW a B C + avgW a B D + avgW a C D)) := by
    simp only [G, sum_sub_distrib, sum_add_distrib, sum_trans4_xy, sum_trans4_xw, sum_trans4_xt,
      sum_trans4_yw, sum_trans4_yt, sum_trans4_wt, sum_const, card_product, nsmul_eq_mul,
      hcard nA nB, hcard nA nC, hcard nA nD, hcard nB nC, hcard nB nD, hcard nC nD]
    push_cast; ring
  have hpos : (0:ℝ) ≤ (A.card : ℝ) * B.card * C.card * D.card := by positivity
  -- Markov
  have hM := card_filter_mul_le (trans4 A B C D) G (fun z hz' => (hz z hz').1) r0
  have hbad : ((((A ×ˢ B) ×ˢ (C ×ˢ D)).filter fun z =>
      r0 < |a z.1.1 z.1.2 - a z.2.1 z.2.2|).card : ℝ) ≤
      e / r0 * (A ×ˢ B).card * (C ×ˢ D).card := by
    have hsub : (((A ×ˢ B) ×ˢ (C ×ˢ D)).filter fun z => r0 < |a z.1.1 z.1.2 - a z.2.1 z.2.2|) ⊆
        (trans4 A B C D).filter fun z => r0 < G z := by
      intro z hz'
      rw [mem_filter] at hz' ⊢
      exact ⟨hz'.1, lt_of_lt_of_le hz'.2 (hz z hz'.1).2⟩
    have h1 := card_le_card hsub
    have h2 : (((trans4 A B C D).filter fun z => r0 < G z).card : ℝ) ≤
        e / r0 * (A ×ˢ B).card * (C ×ˢ D).card := by
      rw [card_product, card_product]; push_cast
      have : (((trans4 A B C D).filter fun z => r0 < G z).card : ℝ) * r0 ≤
          (A.card : ℝ) * B.card * C.card * D.card * e := by
        rw [hsumG] at hM
        calc _ ≤ _ := hM
          _ ≤ _ := mul_le_mul_of_nonneg_left hslack hpos
      calc (((trans4 A B C D).filter fun z => r0 < G z).card : ℝ)
          = (((trans4 A B C D).filter fun z => r0 < G z).card : ℝ) * r0 / r0 := by
            field_simp
        _ ≤ (A.card : ℝ) * B.card * C.card * D.card * e / r0 :=
            div_le_div_of_nonneg_right this hr0.le
        _ = e / r0 * (A.card * B.card) * (C.card * D.card) := by ring
    calc _ ≤ (((trans4 A B C D).filter fun z => r0 < G z).card : ℝ) := by exact_mod_cast h1
      _ ≤ _ := h2
  have hc := conc_of_split (A ×ˢ B) (C ×ˢ D) (fun p => a p.1 p.2) (fun r => a r.1 r.2)
    (fun p => H.nonneg _ _) (fun p => H.le_one _ _) (fun r => H.nonneg _ _)
    (fun r => H.le_one _ _) hr0.le (nC.product nD) hbad
  have havg : (∑ q ∈ A ×ˢ B, a q.1 q.2) / ((A ×ˢ B).card : ℝ) = avgW a A B := by
    rw [sum_product, card_product]; unfold avgW bsum; push_cast; rfl
  rw [havg, card_product] at hc
  push_cast at hc
  calc _ ≤ e / r0 * ((A.card : ℝ) * B.card) := hc
    _ = _ := by ring

end NashWilliams.Frac
