/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.Fractional.FourPoint

/-!
# Lemma 4.29 of Delcourt–Postle (the value lemma), in Lagrangian form

If `a` is a symmetric `[0,1]`-weighting on a finite set `S` (zero on the diagonal) that is
triangle-thin (every three distinct points carry total weight at most `2`) and whose support
contains no `K₅`, then for every nonnegative vector `y`,
`∑_{i,j ∈ S} a i j y i y j ≤ (∑_{i ∈ S} y i)^2 / 2`.

Taking `y ≡ 1` gives `∑_{i,j} a i j ≤ |S|^2 / 2`, i.e. `|φ| ≤ |S|^2/4` in the paper's notation.
The proof shifts mass between non-adjacent points (Motzkin–Straus style) until the support is a
clique, which has at most four points, and then applies Lemma 5.2.
-/

namespace NashWilliams.Frac

open Finset

variable {α : Type*} [DecidableEq α]

/-- The quadratic form `∑_{i,j ∈ S} a i j y i y j`. -/
def quadF (S : Finset α) (a : α → α → ℝ) (y : α → ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S, a i j * y i * y j

/-- Hypotheses of the value lemma. -/
structure ThinWeights (S : Finset α) (a : α → α → ℝ) : Prop where
  symm : ∀ i j, a i j = a j i
  diag : ∀ i, a i i = 0
  nonneg : ∀ i j, 0 ≤ a i j
  le_one : ∀ i j, a i j ≤ 1
  thin : ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k → a i j + a i k + a j k ≤ 2
  clique : ∀ T ⊆ S, (∀ i ∈ T, ∀ j ∈ T, i ≠ j → 0 < a i j) → T.card ≤ 4

lemma quadF_small (S : Finset α) (a : α → α → ℝ) (H : ThinWeights S a) (T : Finset α)
    (hTS : T ⊆ S) (hT : T.card ≤ 4) (y : α → ℝ) (hy : ∀ i, 0 ≤ y i) :
    quadF T a y ≤ (∑ i ∈ T, y i) ^ 2 / 2 := by
  have th : ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, i ≠ j → i ≠ k → j ≠ k → a i j + a i k + a j k ≤ 2 :=
    fun i hi j hj k hk => H.thin i (hTS hi) j (hTS hj) k (hTS hk)
  interval_cases h : T.card
  · rw [card_eq_zero] at h; subst h; simp [quadF]
  · obtain ⟨p, rfl⟩ := card_eq_one.1 h
    simp [quadF, H.diag]; positivity
  · obtain ⟨p, q, hpq, rfl⟩ := card_eq_two.1 h
    simp only [quadF, sum_insert, mem_singleton, hpq, not_false_eq_true, sum_singleton, H.diag]
    rw [H.symm q p]
    nlinarith [four_point (y p) (y q) 0 0 (a p q) 0 0 0 0 0 (hy p) (hy q) le_rfl le_rfl
      (H.le_one p q) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by linarith [H.le_one p q]) (by linarith [H.le_one p q]) (by norm_num) (by norm_num)]
  · obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := card_eq_three.1 h
    simp only [quadF, sum_insert, mem_insert, mem_singleton, hpq, hpr, hqr, or_self,
      not_false_eq_true, sum_singleton, H.diag]
    rw [H.symm q p, H.symm r p, H.symm r q]
    have t := th p (by simp) q (by simp) r (by simp) hpq hpr hqr
    nlinarith [four_point (y p) (y q) (y r) 0 (a p q) (a p r) 0 (a q r) 0 0 (hy p) (hy q) (hy r)
      le_rfl (H.le_one p q) (H.le_one p r) (by norm_num) (H.le_one q r) (by norm_num)
      (by norm_num) t (by linarith [H.le_one p q]) (by linarith [H.le_one p r])
      (by linarith [H.le_one q r])]
  · obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, rfl⟩ := card_eq_four.1 h
    simp only [quadF, sum_insert, mem_insert, mem_singleton, hpq, hpr, hps, hqr, hqs, hrs,
      or_self, not_false_eq_true, sum_singleton, H.diag]
    rw [H.symm q p, H.symm r p, H.symm s p, H.symm r q, H.symm s q, H.symm s r]
    have t1 := th p (by simp) q (by simp) r (by simp) hpq hpr hqr
    have t2 := th p (by simp) q (by simp) s (by simp) hpq hps hqs
    have t3 := th p (by simp) r (by simp) s (by simp) hpr hps hrs
    have t4 := th q (by simp) r (by simp) s (by simp) hqr hqs hrs
    nlinarith [four_point (y p) (y q) (y r) (y s) (a p q) (a p r) (a p s) (a q r) (a q s) (a r s)
      (hy p) (hy q) (hy r) (hy s) (H.le_one p q) (H.le_one p r) (H.le_one p s) (H.le_one q r)
      (H.le_one q s) (H.le_one r s) t1 t2 t3 t4]

/-- Shifting mass along `δ = e_i - e_j` changes the quadratic form linearly when `a i j = 0`. -/
lemma quadF_shift (S : Finset α) (a : α → α → ℝ) (H : ThinWeights S a) (y : α → ℝ)
    {i j : α} (hi : i ∈ S) (hj : j ∈ S) (ha : a i j = 0) (c : ℝ) :
    quadF S a (fun k => y k + c * ((if k = i then 1 else 0) - (if k = j then 1 else 0))) =
      quadF S a y + 2 * c * (∑ l ∈ S, a i l * y l - ∑ l ∈ S, a j l * y l) := by
  set δ : α → ℝ := fun k => (if k = i then 1 else 0) - (if k = j then 1 else 0) with hδ
  have hsum : ∀ g : α → ℝ, ∑ k ∈ S, δ k * g k = g i - g j := by
    intro g
    simp only [hδ, sub_mul, ite_mul, one_mul, zero_mul, sum_sub_distrib, sum_ite_eq', hi, hj,
      if_true]
  have e : ∀ k l, a k l * (y k + c * δ k) * (y l + c * δ l) =
      a k l * y k * y l + c * (δ k * (a k l * y l)) + c * (δ l * (a l k * y k)) +
        c ^ 2 * (δ k * (δ l * a k l)) := by
    intro k l; rw [H.symm l k]; ring
  show quadF S a (fun k => y k + c * δ k) = _
  unfold quadF
  have h2 : ∀ k ∈ S, ∑ l ∈ S, a k l * (y k + c * δ k) * (y l + c * δ l) =
      ∑ l ∈ S, a k l * y k * y l + c * (δ k * ∑ l ∈ S, a k l * y l) +
        c * ∑ l ∈ S, δ l * (a l k * y k) + c ^ 2 * (δ k * ∑ l ∈ S, δ l * a k l) := by
    intro k _
    simp only [e, sum_add_distrib, mul_sum]
  rw [sum_congr rfl h2]
  simp only [sum_add_distrib]
  rw [← mul_sum, ← mul_sum, ← mul_sum]
  rw [sum_comm (s := S) (t := S) (f := fun k l => δ l * (a l k * y k))]
  have h3 : ∀ l ∈ S, ∑ k ∈ S, δ l * (a l k * y k) = δ l * ∑ k ∈ S, a l k * y k := by
    intro l _; rw [mul_sum]
  rw [sum_congr rfl h3, hsum (fun k => ∑ l ∈ S, a k l * y l),
    hsum (fun k => ∑ l ∈ S, δ l * a k l), hsum (fun l => a i l), hsum (fun l => a j l),
    H.diag, H.diag, ha, H.symm j i, ha]
  ring

theorem value_lemma (S : Finset α) (a : α → α → ℝ) (H : ThinWeights S a) (y : α → ℝ)
    (hy : ∀ i, 0 ≤ y i) : quadF S a y ≤ (∑ i ∈ S, y i) ^ 2 / 2 := by
  induction hn : (S.filter (fun i => y i ≠ 0)).card using Nat.strong_induction_on
    generalizing y with
  | _ n ih =>
  set T := S.filter (fun i => y i ≠ 0) with hT
  by_cases hc : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → 0 < a i j
  · have hT4 := H.clique T (filter_subset _ _) hc
    have e1 : quadF S a y = quadF T a y := by
      unfold quadF
      rw [hT, sum_filter_of_ne]
      · apply sum_congr rfl; intro i _
        rw [sum_filter_of_ne]
        intro j _ h hj; apply h; rw [hj]; ring
      · intro i _ h hi; apply h; simp [hi]
    have e2 : ∑ i ∈ S, y i = ∑ i ∈ T, y i := by
      rw [hT, sum_filter_ne_zero]
    rw [e1, e2]
    exact quadF_small S a H T (filter_subset _ _) hT4 y hy
  · push_neg at hc
    obtain ⟨i, hi, j, hj, hij, ha⟩ := hc
    have ha0 : a i j = 0 := le_antisymm ha (H.nonneg i j)
    have hiS : i ∈ S := (mem_filter.1 hi).1
    have hjS : j ∈ S := (mem_filter.1 hj).1
    set D := ∑ l ∈ S, a i l * y l - ∑ l ∈ S, a j l * y l
    -- generic facts about a shift
    have key : ∀ c : ℝ, ∀ m : α, m ∈ T →
        (y m + c * ((if m = i then 1 else 0) - (if m = j then 1 else 0)) = 0) →
        (∀ k, 0 ≤ y k + c * ((if k = i then 1 else 0) - (if k = j then 1 else 0))) →
        quadF S a (fun k => y k + c * ((if k = i then 1 else 0) - (if k = j then 1 else 0))) ≤
          (∑ k ∈ S, (y k + c * ((if k = i then 1 else 0) - (if k = j then 1 else 0)))) ^ 2 /
            2 := by
      intro c m hm hm0 hnn
      refine ih _ ?_ _ hnn rfl
      rw [← hn]
      apply card_lt_card
      refine ⟨?_, fun h => ?_⟩
      · intro k hk
        rw [mem_filter] at hk ⊢
        refine ⟨hk.1, fun hk0 => hk.2 ?_⟩
        by_cases hki : k = i
        · subst hki; exact absurd hk0 (mem_filter.1 hi).2
        by_cases hkj : k = j
        · subst hkj; exact absurd hk0 (mem_filter.1 hj).2
        simp [hki, hkj, hk0]
      · have := h hm
        rw [mem_filter] at this
        exact this.2 hm0
    have hsum : ∀ c : ℝ, ∑ k ∈ S, (y k + c * ((if k = i then 1 else 0) -
        (if k = j then 1 else 0))) = ∑ k ∈ S, y k := by
      intro c
      simp [sum_add_distrib, ← mul_sum, sum_sub_distrib, sum_ite_eq', hiS, hjS]
    have hyi := hy i
    have hyj := hy j
    rcases le_total 0 D with hD | hD
    · have h1 := key (y j) j hj (by simp [Ne.symm hij]) (by
        intro k; by_cases hki : k = i
        · subst hki; simp [hij]; linarith
        by_cases hkj : k = j
        · subst hkj; simp [Ne.symm hij]
        simp [hki, hkj, hy k])
      rw [quadF_shift S a H y hiS hjS ha0, hsum] at h1
      nlinarith [mul_nonneg hyj hD]
    · have h1 := key (-y i) i hi (by simp [hij]) (by
        intro k; by_cases hki : k = i
        · subst hki; simp [hij]
        by_cases hkj : k = j
        · subst hkj; simp [Ne.symm hij]; linarith
        simp [hki, hkj, hy k])
      rw [quadF_shift S a H y hiS hjS ha0, hsum] at h1
      nlinarith [mul_nonneg hyi (neg_nonneg.2 hD)]

end NashWilliams.Frac
