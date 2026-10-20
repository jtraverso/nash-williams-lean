/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.StabNum
import RequestProject.FracStab.StabCut

/-!
# Value stability for thin weightings (Lemma 8.10, in the form used for Lemma 9.5)
-/

namespace NashWilliams.Frac

open Finset

section

variable {α : Type*} [DecidableEq α] {S : Finset α} {a : α → α → ℝ}

/-- The greedy partition, with classes sorted by decreasing size. -/
lemma exists_sorted_part (H : ThinWeights S a) :
    ∃ Y : Fin 4 → Finset α, Part4 S Y ∧
      (∀ i, bsum a (Y i) (Y i) ≤ (S.card : ℝ) ^ 2 / 2 - bsum a S S) ∧
      (Y 3).card ≤ (Y 2).card ∧ (Y 2).card ≤ (Y 1).card ∧ (Y 1).card ≤ (Y 0).card := by
  obtain ⟨X, hsub, hdisj, hcov, hin⟩ := greedy_partition H
  obtain ⟨σ, hmono⟩ : ∃ σ : Equiv.Perm (Fin 4),
      Monotone ((fun i => -((X i).card : ℤ)) ∘ σ) := ⟨_, Tuple.monotone_sort _⟩
  have hle : ∀ i j : Fin 4, i ≤ j → (X (σ j)).card ≤ (X (σ i)).card := by
    intro i j hij
    have := hmono hij
    simp only [Function.comp] at this
    omega
  refine ⟨fun i => X (σ i), ⟨fun i => hsub _, fun i j hij => hdisj _ _ (σ.injective.ne hij),
    fun x hx => ?_⟩, fun i => hin _, hle _ _ (by decide), hle _ _ (by decide),
    hle _ _ (by decide)⟩
  obtain ⟨i, hi⟩ := hcov x hx
  exact ⟨σ.symm i, by simpa using hi⟩

/-- The normalised configuration of a partition. -/
lemma cfg_of_part (H : ThinWeights S a) {Y : Fin 4 → Finset α} (P : Part4 S Y)
    (hc : 0 < (S.card : ℝ)) :
    Cfg4 (fun i => ((Y i).card : ℝ) / S.card) (fun i j => avgW a (Y i) (Y j)) where
  x0 := fun i => by positivity
  sum := by
    have := P.card_eq; rw [Fin.sum_univ_four] at this
    field_simp; linarith
  symm := fun i j => avgW_comm H.symm _ _
  nonneg := fun i j => avgW_nonneg H.nonneg _ _
  le1 := fun i j => avgW_le_one H.le_one _ _
  thin := fun i j k hij hik hjk =>
    avgW_thin H (P.sub i) (P.sub j) (P.sub k) (P.disj _ _ hij) (P.disj _ _ hik) (P.disj _ _ hjk)

omit [DecidableEq α] in
lemma bsum_eq_cfg {Y : Fin 4 → Finset α} (hc : 0 < (S.card : ℝ)) (i j : Fin 4) :
    bsum a (Y i) (Y j) = avgW a (Y i) (Y j) * (((Y i).card : ℝ) / S.card) *
      (((Y j).card : ℝ) / S.card) * (S.card : ℝ) ^ 2 := by
  rw [bsum_eq_avgW']; field_simp

/-- Value decomposition along a partition. -/
lemma bsum_eq_val (H : ThinWeights S a) {Y : Fin 4 → Finset α} (P : Part4 S Y)
    (hc : 0 < (S.card : ℝ)) :
    bsum a S S = ∑ i, bsum a (Y i) (Y i) + 2 * (S.card : ℝ) ^ 2 *
      valS (fun i => ((Y i).card : ℝ) / S.card) (fun i j => avgW a (Y i) (Y j)) := by
  rw [P.bsum_eq]
  simp only [Fin.sum_univ_four, val4]
  have e := fun i j => bsum_eq_cfg (a := a) (Y := Y) hc i j
  have c := fun i j => bsum_comm H.symm (Y i) (Y j)
  rw [c 1 0, c 2 0, c 3 0, c 2 1, c 3 1, c 3 2, e 0 1, e 0 2, e 0 3, e 1 2, e 1 3, e 2 3]
  ring

end

/-- **Value stability (Lemma 8.10).** -/
theorem thin_stability {δ : ℝ} (hδ : 0 < δ) :
    ∃ κ > 0, κ ≤ 1 ∧ ∃ τ > 0, τ ≤ 1/16 ∧ ∀ θ > 0, ∃ ε > 0, ∀ {α : Type} [DecidableEq α] (S : Finset α)
      (a : α → α → ℝ), ThinWeights S a → (1 - ε) * (S.card : ℝ) ^ 2 / 2 ≤ bsum a S S →
      CutStruct S a δ ∨ QuadStruct S a κ τ θ := by
  set δ' := min δ (1/2) with hδ'def
  have hδ'0 : 0 < δ' := by positivity
  have hδ'1 : δ' ≤ 1/2 := min_le_right _ _
  have hδ'δ : δ' ≤ δ := min_le_left _ _
  refine ⟨δ'^2/24, by positivity, by nlinarith, δ'^2/16, by positivity, by nlinarith,
    fun θ hθ => ?_⟩
  obtain ⟨ρ, hρ, hnum⟩ := stab_numeric hδ'0 hδ'1 hθ
  refine ⟨ρ^2/2, by positivity, fun {α} _ S a H hval => ?_⟩
  rcases (Nat.cast_nonneg (α := ℝ) S.card).lt_or_eq with hc | hc
  swap
  · left
    have hS : S = ∅ := by rw [← card_eq_zero]; exact_mod_cast hc.symm
    subst hS
    exact ⟨∅, Subset.refl _, by simp, by simp, by simp⟩
  obtain ⟨Y, P, hin, h32, h21, h10⟩ := exists_sorted_part H
  have hdec := bsum_eq_val H P hc
  have Hc := cfg_of_part H P hc
  obtain ⟨x, hxdef⟩ : ∃ x : Fin 4 → ℝ, x = fun i => ((Y i).card : ℝ) / S.card := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ m : Fin 4 → Fin 4 → ℝ, m = fun i j => avgW a (Y i) (Y j) := ⟨_, rfl⟩
  rw [← hxdef, ← hmdef] at hdec Hc
  have hxY : ∀ i, ((Y i).card : ℝ) = x i * S.card := fun i => by
    rw [hxdef]; field_simp
  have hx : ∀ i j, (Y i).card ≤ (Y j).card → x i ≤ x j := fun i j h => by
    rw [hxdef]; exact div_le_div_of_nonneg_right (by exact_mod_cast h) hc.le
  have hv : 1/4 - ρ^2 ≤ valS x m := by
    have hsum : ∑ i, bsum a (Y i) (Y i) ≤ 4 * ((S.card : ℝ) ^ 2 / 2 - bsum a S S) := by
      rw [Fin.sum_univ_four]; linarith [hin 0, hin 1, hin 2, hin 3]
    have hc2 : 0 < (S.card : ℝ) ^ 2 := pow_pos hc 2
    have key : (1/4 - ρ^2) * (S.card : ℝ) ^ 2 ≤ valS x m * (S.card : ℝ) ^ 2 := by
      have h5 : 0 ≤ ρ ^ 2 * (S.card : ℝ) ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      linarith only [hdec, hsum, hval, h5]
    exact le_of_mul_le_mul_right key hc2
  rcases hnum x m Hc (hx 3 2 h32) (hx 2 1 h21) (hx 1 0 h10) hv with hcut | hquad
  · -- a cut
    left
    obtain ⟨I, hbal, hbad⟩ := hcut
    refine CutStruct.mono (P.cut_of_blocks H.le_one I hδ'0 ?_ ?_) hδ'δ
    · have : ∑ i ∈ I, ((Y i).card : ℝ) - S.card / 2 = (∑ i ∈ I, x i - 1/2) * S.card := by
        simp only [hxY, ← sum_mul]; ring
      rw [this, abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_right hbal hc.le
    · have : ∑ i ∈ I, ∑ j ∈ Iᶜ, (((Y i).card : ℝ) * (Y j).card - bsum a (Y i) (Y j)) =
          (∑ i ∈ I, ∑ j ∈ Iᶜ, (1 - m i j) * x i * x j) * (S.card : ℝ) ^ 2 := by
        rw [sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun j _ => ?_
        rw [bsum_eq_avgW', hxY i, hxY j]; simp only [hmdef]; ring
      rw [this]; exact mul_le_mul_of_nonneg_right hbad (sq_nonneg _)
  · -- a nearly matched four part structure
    right
    obtain ⟨qκ, qτ, qm, qt, qb, qs⟩ := hquad
    refine ⟨Y, m, P.sub, P.disj, P.cover, fun i => ?_, Hc.symm, fun i j hij => ⟨qτ i j hij,
      Hc.le1 i j⟩, qm, fun i j k hij hik hjk => ?_, fun i j k l hij hik hil hjk hjl hkl hm => ?_,
      fun i j hij => ?_⟩
    · rw [hxY]; exact mul_le_mul_of_nonneg_right (qκ i) hc.le
    · have := Hc.thin i j k hij hik hjk
      have := qt i j k hij hik hjk
      rw [abs_le]; constructor <;> linarith
    · have : ((Y i).card + (Y j).card : ℝ) - S.card / 2 = (x i + x j - 1/2) * S.card := by
        rw [hxY, hxY]; ring
      rw [this, abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_right (qb i j k l hij hik hil hjk hjl hkl hm) hc.le
    · obtain ⟨k, l, hik, hil, hjk, hjl, hkl⟩ := exists_other_two hij
      have hne : ∀ t, (Y t).Nonempty := fun t => by
        rw [← card_pos]
        have := qκ t
        have h1 : 0 < x t := lt_of_lt_of_le (div_pos (pow_pos hδ'0 2) (by norm_num)) this
        have h2 : (0:ℝ) < (Y t).card := by rw [hxY]; exact mul_pos h1 hc
        exact_mod_cast h2
      have hslack : 4 - (avgW a (Y i) (Y j) + avgW a (Y i) (Y k) + avgW a (Y i) (Y l) +
          avgW a (Y j) (Y k) + avgW a (Y j) (Y l) + avgW a (Y k) (Y l)) ≤ θ ^ 2 / 8 := by
        have := sum6_perm Hc.symm hij hik hil hjk hjl hkl
        simp only [sum6, hmdef] at this qs
        linarith
      have hcp := conc_pair H (P.sub i) (P.sub j) (P.sub k) (P.sub l) (P.disj _ _ hij)
        (P.disj _ _ hik) (P.disj _ _ hil) (P.disj _ _ hjk) (P.disj _ _ hjl) (P.disj _ _ hkl)
        (hne i) (hne j) (hne k) (hne l) (r0 := θ / 4) (by positivity) hslack
      have e1 : 2 * (θ / 4) + θ ^ 2 / 8 / (θ / 4) = θ := by field_simp; ring
      have e2 : θ ^ 2 / 8 / (θ / 4) = θ / 2 := by field_simp; ring
      simp only [e2] at hcp
      have e3 : 2 * (θ / 4) + θ / 2 = θ := by ring
      simp only [e3] at hcp
      simp only [hmdef]
      have hYi : ((Y i).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card (P.sub i)
      have hYj : ((Y j).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card (P.sub j)
      have hb : ((Y i).card : ℝ) * (Y j).card ≤ (S.card : ℝ) ^ 2 := by
        rw [sq]; exact mul_le_mul hYi hYj (Nat.cast_nonneg _) hc.le
      calc _ ≤ θ / 2 * ((Y i).card : ℝ) * (Y j).card := hcp
        _ = θ / 2 * (((Y i).card : ℝ) * (Y j).card) := by ring
        _ ≤ θ / 2 * (S.card : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hb (by positivity)
        _ ≤ θ * (S.card : ℝ) ^ 2 := by nlinarith

end NashWilliams.Frac
