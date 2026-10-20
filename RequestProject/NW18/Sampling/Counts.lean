/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Sampling.Prob

@[expose] public section

/-!
# Concentration of counts in a uniformly random sequence

For a uniformly random sequence `ω : Fin m → α`:

* `count_lower`: the number of coordinates satisfying a predicate `g` is, with high
  probability, not much smaller than its mean `m · |g| / N`;
* `deg_lower`: with high probability, simultaneously for every coordinate `i`, the number of
  coordinates `j` with `R (ω i) (ω j)` is not much smaller than `(m - 1) · deg_R(ω i) / N`.
-/

namespace NashWilliams18.Sampling

open Finset Pseudorandom

variable {α : Type*} [Fintype α] [Nonempty α]

omit [Fintype α] [Nonempty α] in
/-- A sum of functions of single coordinates has bounded differences. -/
lemma coordGap_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → α → ℝ) (c : ι → ℝ)
    (hφ : ∀ j a b, |φ j a - φ j b| ≤ c j) :
    CoordGap (fun ω : ι → α => ∑ j, φ j (ω j)) c := by
  intro i ω a b
  rw [← sum_sub_distrib, sum_eq_single i]
  · simpa using hφ i a b
  · intro j _ hj
    simp [Function.update_of_ne hj]
  · simp

/-- Expectation of a sum of functions of single coordinates. -/
lemma pE_sum_coord {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : ι → α → ℝ) :
    pE (unif ι α) (fun ω => ∑ j, φ j (ω j)) =
      ∑ j, (∑ a, φ j a) / Fintype.card α := by
  rw [pE_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [pE_coord unif_isPMF j]
  simp only [unif]
  rw [← mul_sum]
  ring

omit [Fintype α] [Nonempty α] in
lemma exp_mono_aux {t A B : ℝ} (hA : 0 < A + t) (hAB : A ≤ B) :
    Real.exp (-(t ^ 2 / (2 * (A + t)))) ≤ Real.exp (-(t ^ 2 / (2 * (B + t)))) := by
  apply Real.exp_le_exp.mpr
  apply neg_le_neg
  apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- **Counts concentrate (lower tail).** -/
lemma count_lower (m : ℕ) (g : α → Prop) [DecidablePred g] (t : ℝ) (ht : 0 < t) :
    pProb (unif (Fin m) α) (fun ω =>
      (((univ.filter fun j => g (ω j)).card : ℕ) : ℝ) <
        m * ((univ.filter g).card : ℝ) / Fintype.card α - t) ≤
      Real.exp (-(t ^ 2 / (2 * (m + t)))) := by
  set φ : Fin m → α → ℝ := fun _ a => if g a then 1 else 0
  have hcount : ∀ ω : Fin m → α,
      (((univ.filter fun j => g (ω j)).card : ℕ) : ℝ) = ∑ j, φ j (ω j) := by
    intro ω; simp [φ, Finset.sum_boole]
  have hmean : pE (unif (Fin m) α) (fun ω => ∑ j, φ j (ω j)) =
      m * ((univ.filter g).card : ℝ) / Fintype.card α := by
    rw [pE_sum_coord]
    simp [φ, Finset.sum_boole]
    ring
  have h := lower_tail unif_isPMF (fun ω => ∑ j, φ j (ω j)) (fun _ => 1) 1 one_pos
    (fun _ => ⟨zero_le_one, le_rfl⟩)
    (coordGap_sum φ _ fun j a b => by
      simp only [φ]; split_ifs <;> norm_num) t ht
  simp only [one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    one_mul] at h
  refine le_trans (pProb_mono unif_isPMF fun ω hω => ?_) h
  rw [hmean]
  rw [hcount] at hω
  linarith

/-- **Degrees in the sample concentrate (lower tail), for one coordinate.** -/
lemma deg_lower_one (m : ℕ) (R : α → α → Prop) [DecidableRel R] (hR : ∀ a, ¬ R a a)
    (i : Fin m) (t : ℝ) (ht : 0 < t) :
    pProb (unif (Fin m) α) (fun ω =>
      (((univ.filter fun j => R (ω i) (ω j)).card : ℕ) : ℝ) <
        (m - 1) * ((univ.filter (R (ω i))).card : ℝ) / Fintype.card α - t) ≤
      Real.exp (-(t ^ 2 / (2 * (m + t)))) := by
  refine pProb_le_of_update unif_isPMF i _ _ fun a => ?_
  simp only [Function.update_self]
  set φ : Fin m → α → ℝ := fun j b => if j = i then 0 else if R a b then 1 else 0
  have hcount : ∀ ω : Fin m → α,
      (((univ.filter fun j => R a (Function.update ω i a j)).card : ℕ) : ℝ) =
        ∑ j, φ j (ω j) := by
    intro ω
    rw [Finset.card_filter]
    push_cast
    refine sum_congr rfl fun j _ => ?_
    by_cases hj : j = i
    · subst hj; simp [φ, hR]
    · simp [φ, hj]
  have hmean : pE (unif (Fin m) α) (fun ω => ∑ j, φ j (ω j)) =
      (m - 1) * ((univ.filter (R a)).card : ℝ) / Fintype.card α := by
    rw [pE_sum_coord]
    have : ∀ j, (∑ b, φ j b) = if j = i then 0 else ((univ.filter (R a)).card : ℝ) := by
      intro j
      by_cases hj : j = i
      · simp [φ, hj]
      · simp [φ, hj, Finset.sum_boole]
    simp_rw [this]
    rw [← sum_div]
    rw [Finset.sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul]
    congr 2
    have : (univ.filter fun j : Fin m => ¬ j = i) = univ.erase i := by
      ext j; simp
    rw [this, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
    push_cast [this]
    ring
  have hc : ∀ j : Fin m, 0 ≤ (if j = i then (0 : ℝ) else 1) ∧ (if j = i then (0 : ℝ) else 1) ≤ 1 :=
    fun j => by split_ifs <;> norm_num
  have h := lower_tail unif_isPMF (fun ω => ∑ j, φ j (ω j)) (fun j => if j = i then 0 else 1) 1
    one_pos hc
    (coordGap_sum φ _ fun j a b => by
      simp only [φ]; split_ifs <;> norm_num) t ht
  have hsum : ∑ j : Fin m, (if j = i then (0 : ℝ) else 1) ^ 2 ≤ m :=
    calc ∑ j : Fin m, (if j = i then (0 : ℝ) else 1) ^ 2
          ≤ ∑ _j : Fin m, (1 : ℝ) := sum_le_sum fun j _ => by split_ifs <;> norm_num
        _ = m := by simp
  have hnn : 0 ≤ ∑ j : Fin m, (if j = i then (0 : ℝ) else 1) ^ 2 :=
    sum_nonneg fun j _ => sq_nonneg _
  simp only [one_mul] at h
  have h' := h.trans (exp_mono_aux (by linarith) hsum)
  refine le_trans (pProb_mono unif_isPMF fun ω hω => ?_) h'
  rw [hmean]; rw [hcount] at hω; linarith

/-- **Degrees in the sample concentrate, for all coordinates simultaneously.** -/
lemma deg_lower (m : ℕ) (R : α → α → Prop) [DecidableRel R] (hR : ∀ a, ¬ R a a)
    (t : ℝ) (ht : 0 < t) :
    pProb (unif (Fin m) α) (fun ω => ∃ i,
      (((univ.filter fun j => R (ω i) (ω j)).card : ℕ) : ℝ) <
        (m - 1) * ((univ.filter (R (ω i))).card : ℝ) / Fintype.card α - t) ≤
      m * Real.exp (-(t ^ 2 / (2 * (m + t)))) := by
  have h := pProb_exists_le unif_isPMF (univ : Finset (Fin m)) (fun i ω =>
      (((univ.filter fun j => R (ω i) (ω j)).card : ℕ) : ℝ) <
        (m - 1) * ((univ.filter (R (ω i))).card : ℝ) / Fintype.card α - t)
  refine le_trans ?_ (h.trans ?_)
  · exact le_of_eq (pProb_congr fun ω => by simp)
  · calc ∑ i ∈ (univ : Finset (Fin m)), pProb (unif (Fin m) α) _
        ≤ ∑ _i ∈ (univ : Finset (Fin m)), Real.exp (-(t ^ 2 / (2 * (m + t)))) :=
          sum_le_sum fun i _ => deg_lower_one m R hR i t ht
      _ = _ := by simp

end NashWilliams18.Sampling
