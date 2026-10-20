/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.Conflicts

/-! # The load of an untouched edge after one round

Fix an active edge `e`. Its survival event is "every coin of a triangle through
`e` is zero". On that specified product event the surviving-triangle load
equals `fe`, a function of the remaining coins only. By `cubeMean_zeroing` the
conditioned law is the product law with the coins through `e` set to zero, the
other coins keeping their original probabilities. We compute the mean of `fe`
under this law from the product formula, bound it by the logarithmic product
estimate, and apply the rare-coordinate concentration theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.Nibble

open BernoulliExposure BernoulliConcentration Finset

variable {V : Type*} [DecidableEq V] {m : ℕ}

/-- Load of the surviving (untouched) triangles through `e`. -/
noncomputable def availLoad (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (e : Sym2 V) (ω : Fin m → Bool) : ℝ :=
  ∑ i ∈ (S.edgeTris e).filter (fun i => triEdges (S.tri i) ⊆ S.untouched B ω), w i

/-- The surviving load written with outside coins only. -/
noncomputable def fe (S : TriSystem V m) (w : Fin m → ℝ) (e : Sym2 V) (ω : Fin m → Bool) : ℝ :=
  ∑ i ∈ S.edgeTris e, (if ∀ j ∈ S.outsideNbrs e i, ω j = false then w i else 0)

theorem one_sub_ge_exp (x : ℝ) (h1 : x ≤ 1 / 2) :
    Real.exp (-x - 2 * x ^ 2) ≤ 1 - x := by
  have hpos : 0 < 1 - x := by linarith
  have h2 : -x - 2 * x ^ 2 ≤ -(x / (1 - x)) := by
    rw [neg_le_neg_iff.symm, neg_neg, div_le_iff₀ hpos]
    nlinarith
  have h3 := Real.add_one_le_exp (x / (1 - x))
  have h4 : 1 / (1 - x) = x / (1 - x) + 1 := by field_simp; ring
  have h5 : Real.exp (-(x / (1 - x))) ≤ 1 - x := by
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos _) hpos]
    rw [← one_div, h4]; exact h3
  exact (Real.exp_le_exp.mpr h2).trans h5

theorem mem_untouched_iff (S : TriSystem V m) (B : Finset (Sym2 V)) (e : Sym2 V)
    (ω : Fin m → Bool) : e ∈ S.untouched B ω ↔ e ∈ B ∧ ∀ i ∈ S.edgeTris e, ω i = false := by
  simp only [TriSystem.untouched, TriSystem.touched, mem_sdiff, mem_biUnion, retainedSet,
    mem_filter, mem_univ, true_and, S.mem_edgeTris, not_exists, not_and]
  constructor
  · rintro ⟨hB, h⟩
    exact ⟨hB, fun i hi => by
      by_contra hc
      exact h i (by simpa using hc) hi⟩
  · rintro ⟨hB, h⟩
    exact ⟨hB, fun i hi he => by rw [h i he] at hi; exact absurd hi (by simp)⟩

theorem availLoad_eq_fe (S : TriSystem V m) (B : Finset (Sym2 V)) (w : Fin m → ℝ)
    (hB : ∀ i, triEdges (S.tri i) ⊆ B) (e : Sym2 V) (ω : Fin m → Bool)
    (hω : ∀ i ∈ S.edgeTris e, ω i = false) : availLoad S B w e ω = fe S w e ω := by
  unfold availLoad fe
  rw [sum_filter]
  apply sum_congr rfl
  intro i hi
  congr 1
  apply propext
  constructor
  · intro hsub j hj
    simp only [TriSystem.outsideNbrs, mem_filter, mem_univ, true_and] at hj
    obtain ⟨x, hxi, hxj⟩ := not_disjoint_iff.mp hj.2
    have hx := hsub hxi
    simp only [TriSystem.untouched, TriSystem.touched, mem_sdiff, mem_biUnion, retainedSet,
      mem_filter, mem_univ, true_and, not_exists, not_and] at hx
    by_contra hc
    exact hx.2 j (by simpa using hc) hxj
  · intro h x hx
    simp only [TriSystem.untouched, TriSystem.touched, mem_sdiff, mem_biUnion, retainedSet,
      mem_filter, mem_univ, true_and, not_exists, not_and]
    refine ⟨hB i hx, fun j hj hxj => ?_⟩
    by_cases hje : j ∈ S.edgeTris e
    · rw [hω j hje] at hj; exact absurd hj (by simp)
    · have : j ∈ S.outsideNbrs e i := by
        simp only [TriSystem.outsideNbrs, mem_filter, mem_univ, true_and]
        exact ⟨hje, not_disjoint_iff.mpr ⟨x, hx, hxj⟩⟩
      rw [h j this] at hj; exact absurd hj (by simp)

theorem outsideNbrs_disjoint (S : TriSystem V m) (e : Sym2 V) (i : Fin m) :
    Disjoint (S.edgeTris e) (S.outsideNbrs e i) := by
  rw [Finset.disjoint_left]
  intro j hj hj'
  simp only [TriSystem.outsideNbrs, mem_filter] at hj'
  exact hj'.2.1 hj

theorem fe_indepOf (S : TriSystem V m) (w : Fin m → ℝ) (e : Sym2 V) :
    IndepOf (S.edgeTris e) (fe S w e) := by
  intro ω k b hk
  unfold fe
  apply sum_congr rfl
  intro i _
  congr 1
  apply propext
  apply forall₂_congr
  intro j hj
  have : j ≠ k := fun h => Finset.disjoint_left.mp (outsideNbrs_disjoint S e i) (h ▸ hk) hj
  rw [Function.update_of_ne this]

/-- The conditional mean, from the product formula. -/
theorem cubeMean_fe (S : TriSystem V m) (w : Fin m → ℝ) (q : Fin m → ℝ) (e : Sym2 V) :
    cubeMean (zeroOn q (S.edgeTris e)) (fe S w e) =
      ∑ i ∈ S.edgeTris e, w i * ∏ j ∈ S.outsideNbrs e i, (1 - q j) := by
  classical
  unfold fe
  rw [cubeMean_sum]
  apply sum_congr rfl
  intro i _
  rw [cubeMean_congr _ (g := fun ω => w i *
    (if ∀ j ∈ S.outsideNbrs e i, ω j = false then (1 : ℝ) else 0)) (fun ω => by
      rw [mul_ite, mul_one, mul_zero]), cubeMean_const_mul]
  congr 1
  rw [← cubeProb_def, cubeProb_allZero]
  apply prod_congr rfl
  intro j hj
  have : j ∉ S.edgeTris e := fun h => Finset.disjoint_left.mp (outsideNbrs_disjoint S e i) h hj
  simp [zeroOn, this]

/-- Sensitivity of `fe` to coordinate `j`. -/
noncomputable def feSens (S : TriSystem V m) (w : Fin m → ℝ) (e : Sym2 V) (j : Fin m) : ℝ :=
  ∑ i ∈ (S.edgeTris e).filter (fun i => j ∈ S.outsideNbrs e i), w i

theorem fe_coordBounded (S : TriSystem V m) (w : Fin m → ℝ) (hw : ∀ i, 0 ≤ w i) (e : Sym2 V) :
    CoordBounded (fe S w e) (feSens S w e) := by
  intro j ω
  unfold fe feSens
  rw [← sum_sub_distrib, sum_filter]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  by_cases hj : j ∈ S.outsideNbrs e i
  · rw [ite_eq_left hj]
    split_ifs <;> simp [abs_of_nonneg (hw i), hw i]
  · rw [ite_eq_right hj]
    have : (∀ k ∈ S.outsideNbrs e i, Function.update ω j true k = false) ↔
        (∀ k ∈ S.outsideNbrs e i, Function.update ω j false k = false) := by
      apply forall₂_congr
      intro k hk
      have hkj : k ≠ j := fun h => hj (by rwa [h] at hk)
      rw [Function.update_of_ne hkj, Function.update_of_ne hkj]
    simp only [this, sub_self, abs_zero, le_refl]

namespace RoundHyp

variable {S : TriSystem V m} {B : Finset (Sym2 V)} {w : Fin m → ℝ} {β δ γ : ℝ}
variable (H : RoundHyp S B w β δ γ)
include H

theorem feSens_nonneg (e : Sym2 V) (j : Fin m) : 0 ≤ feSens S w e j :=
  sum_nonneg fun i _ => H.w0 i

theorem feSens_le (e : Sym2 V) (j : Fin m) : feSens S w e j ≤ 3 * β := by
  unfold feSens
  by_cases hj : j ∈ S.edgeTris e
  · rw [filter_false_of_mem (fun i _ hji => by
      simp only [TriSystem.outsideNbrs, mem_filter] at hji; exact hji.2.1 hj), sum_empty]
    linarith [H.β0]
  · have hsub : (S.edgeTris e).filter (fun i => j ∈ S.outsideNbrs e i) ⊆
        (S.edgeTris e).filter (fun i => S.Shares i j) := by
      intro i hi
      simp only [mem_filter, TriSystem.outsideNbrs, mem_univ, true_and] at hi ⊢
      exact ⟨hi.1, hi.2.2⟩
    have hc := (card_le_card hsub).trans (S.card_edgeTris_shares_le hj)
    calc _ ≤ ∑ _i ∈ (S.edgeTris e).filter (fun i => j ∈ S.outsideNbrs e i), β :=
          sum_le_sum fun i _ => H.wβ i
      _ = ((S.edgeTris e).filter (fun i => j ∈ S.outsideNbrs e i)).card * β := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ 3 * β := by
          have : (((S.edgeTris e).filter (fun i => j ∈ S.outsideNbrs e i)).card : ℝ) ≤ 3 := by
            exact_mod_cast hc
          nlinarith [H.β0]

theorem sum_outsideNbrs_le {e : Sym2 V} {i : Fin m} (hi : i ∈ S.edgeTris e) :
    ∑ j ∈ S.outsideNbrs e i, w j ≤ 2 * (1 + δ) := by
  rw [S.sum_outsideNbrs hi]
  calc _ ≤ ∑ _e' ∈ (triEdges (S.tri i)).erase e, (1 + δ) :=
        sum_le_sum fun e' _ => by linarith [H.load_le e', H.w0 i]
    _ = 2 * (1 + δ) := by rw [sum_const, S.card_triEdges_erase hi, nsmul_eq_mul]; push_cast; ring

theorem le_sum_outsideNbrs {e : Sym2 V} {i : Fin m} (hi : i ∈ S.edgeTris e) :
    2 * (1 - δ - β) ≤ ∑ j ∈ S.outsideNbrs e i, w j := by
  rw [S.sum_outsideNbrs hi]
  calc 2 * (1 - δ - β) = ∑ _e' ∈ (triEdges (S.tri i)).erase e, (1 - δ - β) := by
        rw [sum_const, S.card_triEdges_erase hi, nsmul_eq_mul]; push_cast; ring
    _ ≤ _ := sum_le_sum fun e' he' => by
        have := H.load_lo e' (H.hB i (mem_erase.mp he').2)
        linarith [H.wβ i]

/-- Upper bound on the conditional survival probability of a triangle through `e`. -/
theorem survival_le {e : Sym2 V} {i : Fin m} (hi : i ∈ S.edgeTris e) :
    ∏ j ∈ S.outsideNbrs e i, (1 - qv γ w j) ≤ Real.exp (-(2 * γ * (1 - δ - β))) := by
  calc _ ≤ ∏ j ∈ S.outsideNbrs e i, Real.exp (-qv γ w j) := by
        apply prod_le_prod₀
        · intro j _; linarith [(H.hq j).2]
        · intro j _
          have := Real.add_one_le_exp (-qv γ w j); linarith
    _ = Real.exp (-(γ * ∑ j ∈ S.outsideNbrs e i, w j)) := by
        rw [← Real.exp_sum]; congr 1; simp [qv, mul_sum]
    _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have := H.le_sum_outsideNbrs hi
        nlinarith [H.γ0]

/-- Lower bound on the conditional survival probability. -/
theorem survival_ge {e : Sym2 V} {i : Fin m} (hi : i ∈ S.edgeTris e) :
    Real.exp (-(2 * γ * (1 + δ)) - 5 * γ ^ 2 * β) ≤ ∏ j ∈ S.outsideNbrs e i, (1 - qv γ w j) := by
  have hx1 : ∀ j, qv γ w j ≤ γ * β := fun j => mul_le_mul_of_nonneg_left (H.wβ j) H.γ0.le
  have hsum := H.sum_outsideNbrs_le hi
  have hw0 : 0 ≤ ∑ j ∈ S.outsideNbrs e i, w j := sum_nonneg fun j _ => H.w0 j
  calc _ ≤ Real.exp (∑ j ∈ S.outsideNbrs e i, (-qv γ w j - 2 * qv γ w j ^ 2)) := by
        apply Real.exp_le_exp.mpr
        rw [sum_sub_distrib, sum_neg_distrib]
        have h1 : ∑ j ∈ S.outsideNbrs e i, qv γ w j = γ * ∑ j ∈ S.outsideNbrs e i, w j := by
          simp [qv, mul_sum]
        have h2 : ∑ j ∈ S.outsideNbrs e i, 2 * qv γ w j ^ 2 ≤
            2 * (γ * β) * ∑ j ∈ S.outsideNbrs e i, qv γ w j := by
          rw [mul_sum]
          apply sum_le_sum
          intro j _
          have := (H.hq j).1
          nlinarith [hx1 j]
        rw [h1] at h2 ⊢
        have hγ := H.γ0; have hβ := H.β0; have := H.δ1
        have h3 : γ * ∑ j ∈ S.outsideNbrs e i, w j ≤ γ * (2 * (1 + δ)) :=
          mul_le_mul_of_nonneg_left hsum hγ.le
        have h4 : 2 * (γ * β) * (γ * ∑ j ∈ S.outsideNbrs e i, w j) ≤
            2 * (γ * β) * (γ * (2 * (1 + δ))) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
        have h5 : 2 * (γ * β) * (γ * (2 * (1 + δ))) ≤ 5 * γ ^ 2 * β := by
          nlinarith [mul_pos (mul_pos hγ hγ) hβ]
        linarith
    _ = ∏ j ∈ S.outsideNbrs e i, Real.exp (-qv γ w j - 2 * qv γ w j ^ 2) := Real.exp_sum _ _
    _ ≤ _ := by
        apply prod_le_prod₀
        · intro j _; positivity
        · intro j _
          apply one_sub_ge_exp
          have := hx1 j; have := H.γβ; linarith

/-- The conditional mean of the surviving load is near `e^{-2γ}` times one. -/
theorem fe_mean_bounds {e : Sym2 V} (he : e ∈ B) :
    |Real.exp (2 * γ) * cubeMean (zeroOn (qv γ w) (S.edgeTris e)) (fe S w e) - 1| ≤
      (1 + 5 * γ) * δ + 5 * γ * β := by
  rw [cubeMean_fe]
  set μ := ∑ i ∈ S.edgeTris e, w i * ∏ j ∈ S.outsideNbrs e i, (1 - qv γ w j)
  have hlo := H.load_lo e he
  have hhi := H.load_hi e he
  have hγ := H.γ0; have hγ1 := H.γ1; have hδ0 := H.δ0; have hδ1 := H.δ1
  have hβ := H.β0; have hγβ := H.γβ
  have hμhi : μ ≤ (1 + δ) * Real.exp (-(2 * γ * (1 - δ - β))) := by
    calc μ ≤ ∑ i ∈ S.edgeTris e, w i * Real.exp (-(2 * γ * (1 - δ - β))) :=
          sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (H.survival_le hi) (H.w0 i)
      _ = S.load w e * Real.exp (-(2 * γ * (1 - δ - β))) := by rw [← sum_mul]; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_right hhi (Real.exp_pos _).le
  have hμlo : (1 - δ) * Real.exp (-(2 * γ * (1 + δ)) - 5 * γ ^ 2 * β) ≤ μ := by
    calc (1 - δ) * Real.exp (-(2 * γ * (1 + δ)) - 5 * γ ^ 2 * β)
        ≤ S.load w e * Real.exp (-(2 * γ * (1 + δ)) - 5 * γ ^ 2 * β) :=
          mul_le_mul_of_nonneg_right hlo (Real.exp_pos _).le
      _ = ∑ i ∈ S.edgeTris e, w i * Real.exp (-(2 * γ * (1 + δ)) - 5 * γ ^ 2 * β) := by
          rw [← sum_mul]; rfl
      _ ≤ μ := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (H.survival_ge hi) (H.w0 i)
  rw [abs_le]
  constructor
  · -- lower bound
    have hb : 0 ≤ 2 * γ * δ + 5 * γ ^ 2 * β := by positivity
    have h1 : Real.exp (2 * γ) * Real.exp (-(2 * γ * (1 + δ)) - 5 * γ ^ 2 * β) =
        Real.exp (-(2 * γ * δ + 5 * γ ^ 2 * β)) := by rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-(2 * γ * δ + 5 * γ ^ 2 * β))
    have h3 : Real.exp (2 * γ) * ((1 - δ) * Real.exp (-(2 * γ * (1 + δ)) - 5 * γ ^ 2 * β)) ≤
        Real.exp (2 * γ) * μ := mul_le_mul_of_nonneg_left hμlo (Real.exp_pos _).le
    have h4 : γ ^ 2 * β ≤ γ * β := by have := mul_pos hγ hβ; nlinarith
    have h5 : (1 - δ) * (1 - (2 * γ * δ + 5 * γ ^ 2 * β)) ≥
        1 - δ - (2 * γ * δ + 5 * γ ^ 2 * β) := by nlinarith
    nlinarith [Real.exp_pos (-(2 * γ * δ + 5 * γ ^ 2 * β))]
  · -- upper bound
    set a := 2 * γ * δ + 2 * γ * β with ha
    have ha0 : 0 ≤ a := by positivity
    have ha1 : a ≤ 1 := by nlinarith
    have h1 : Real.exp (2 * γ) * Real.exp (-(2 * γ * (1 - δ - β))) = Real.exp a := by
      rw [← Real.exp_add, ha]; ring_nf
    have h2 : Real.exp a ≤ 1 + 2 * a := by
      have := Real.abs_exp_sub_one_sub_id_le (x := a) (by rw [abs_of_nonneg ha0]; exact ha1)
      have := (abs_le.mp this).2
      nlinarith
    have h3 : Real.exp (2 * γ) * μ ≤ (1 + δ) * Real.exp a := by
      rw [← h1]
      calc Real.exp (2 * γ) * μ ≤
          Real.exp (2 * γ) * ((1 + δ) * Real.exp (-(2 * γ * (1 - δ - β)))) :=
            mul_le_mul_of_nonneg_left hμhi (Real.exp_pos _).le
        _ = _ := by ring
    have h4 : (1 + δ) * Real.exp a ≤ (1 + δ) * (1 + 2 * a) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    rw [ha] at h4
    nlinarith

theorem exp_two_gamma_le : Real.exp (2 * γ) ≤ 2 := by
  have h := exp_half_le
  have : Real.exp (2 * γ) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith [H.γ1])
  linarith

/-- Per-edge failure of the load conclusion. -/
theorem load_tail (e : Sym2 V) (ε : ℝ) (hε : 0 < ε) :
    cubeProb (qv γ w) (fun ω => e ∈ S.untouched B ω ∧
        (1 + 5 * γ) * δ + 5 * γ * β + ε < |Real.exp (2 * γ) * availLoad S B w e ω - 1|) ≤
      2 * Real.exp (-((ε / 2) ^ 2 / (2 * (10 * β * γ + 3 * β * (ε / 2))))) := by
  classical
  set q' := zeroOn (qv γ w) (S.edgeTris e)
  have hq' := zeroOn_prob (qv γ w) H.hq (S.edgeTris e)
  set μ := cubeMean q' (fe S w e) with hμ
  have hL : 0 < 3 * β := by linarith [H.β0]
  have hc : ∀ j, 0 ≤ feSens S w e j ∧ feSens S w e j ≤ 3 * β :=
    fun j => ⟨H.feSens_nonneg e j, H.feSens_le e j⟩
  have hV : ∑ j, q' j * feSens S w e j ^ 2 ≤ 10 * β * γ := by
    have h1 : ∑ j, q' j * feSens S w e j ^ 2 ≤ ∑ j, 3 * β * (qv γ w j * feSens S w e j) := by
      apply sum_le_sum
      intro j _
      have hq'j : q' j ≤ qv γ w j := by
        simp only [q', zeroOn]; split_ifs; exacts [(H.hq j).1, le_rfl]
      have h0 := hc j
      have hq0 := (hq' j).1
      rw [sq]
      calc q' j * (feSens S w e j * feSens S w e j) ≤
          qv γ w j * (feSens S w e j * feSens S w e j) :=
            mul_le_mul_of_nonneg_right hq'j (mul_nonneg h0.1 h0.1)
        _ ≤ qv γ w j * (feSens S w e j * (3 * β)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h0.2 h0.1) (H.hq j).1
        _ = _ := by ring
    have h2 : ∑ j, qv γ w j * feSens S w e j =
        γ * ∑ i ∈ S.edgeTris e, w i * ∑ j ∈ S.outsideNbrs e i, w j := by
      simp only [feSens, qv, mul_sum, sum_filter]
      rw [sum_comm]
      apply sum_congr rfl; intro i _
      simp only [mul_ite, mul_zero]
      rw [sum_ite_mem, univ_inter]
      apply sum_congr rfl; intro j _; ring
    have h3 : ∑ i ∈ S.edgeTris e, w i * ∑ j ∈ S.outsideNbrs e i, w j ≤
        S.load w e * (2 * (1 + δ)) := by
      rw [TriSystem.load, sum_mul]
      exact sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (H.sum_outsideNbrs_le hi) (H.w0 i)
    have h4 := H.load_le e
    have hγ := H.γ0; have hβ := H.β0; have := H.δ1; have := H.δ0
    have h5 : S.load w e * (2 * (1 + δ)) ≤ 10 / 3 := by
      have := H.load_nonneg e
      nlinarith
    rw [← mul_sum, h2] at h1
    have h6 : γ * ∑ i ∈ S.edgeTris e, w i * ∑ j ∈ S.outsideNbrs e i, w j ≤ γ * (10 / 3) :=
      mul_le_mul_of_nonneg_left (h3.trans h5) hγ.le
    nlinarith
  have hup := cube_upper_tail q' hq' (fe S w e) (feSens S w e) (3 * β) hL hc
    (fe_coordBounded S w H.w0 e) (ε / 2) (by linarith)
  have hlo := cube_lower_tail q' hq' (fe S w e) (feSens S w e) (3 * β) hL hc
    (fe_coordBounded S w H.w0 e) (ε / 2) (by linarith)
  have hmono := bernstein_mono (ε / 2) (3 * β) _ _ hL (by linarith)
    (sum_nonneg fun j _ => mul_nonneg (hq' j).1 (sq_nonneg _)) hV
  have hsub : ∀ ω, (e ∈ S.untouched B ω ∧
      (1 + 5 * γ) * δ + 5 * γ * β + ε < |Real.exp (2 * γ) * availLoad S B w e ω - 1|) →
      (∀ i ∈ S.edgeTris e, ω i = false) ∧
        (ε / 2 ≤ fe S w e ω - μ ∨ ε / 2 ≤ μ - fe S w e ω) := by
    rintro ω ⟨hu, hbad⟩
    have hz := ((mem_untouched_iff S B e ω).mp hu)
    refine ⟨hz.2, ?_⟩
    rw [availLoad_eq_fe S B w H.hB e ω hz.2] at hbad
    have hm := H.fe_mean_bounds hz.1
    rw [← hμ] at hm
    have hE := H.exp_two_gamma_le
    have hEpos := Real.exp_pos (2 * γ)
    have hdev : ε < Real.exp (2 * γ) * |fe S w e ω - μ| := by
      have : |Real.exp (2 * γ) * fe S w e ω - 1| ≤
          |Real.exp (2 * γ) * μ - 1| + Real.exp (2 * γ) * |fe S w e ω - μ| := by
        rw [← abs_of_pos hEpos, ← abs_mul, abs_of_pos hEpos]
        calc _ = |(Real.exp (2 * γ) * μ - 1) + Real.exp (2 * γ) * (fe S w e ω - μ)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      linarith
    have : ε / 2 < |fe S w e ω - μ| := by nlinarith [abs_nonneg (fe S w e ω - μ)]
    rcases le_or_gt 0 (fe S w e ω - μ) with h | h
    · left; rw [abs_of_nonneg h] at this; linarith
    · right; rw [abs_of_neg h] at this; linarith
  calc _ ≤ cubeProb (qv γ w) (fun ω => (∀ i ∈ S.edgeTris e, ω i = false) ∧
        (ε / 2 ≤ fe S w e ω - μ ∨ ε / 2 ≤ μ - fe S w e ω)) := cubeProb_mono _ H.hq hsub
    _ ≤ cubeProb q' (fun ω => ε / 2 ≤ fe S w e ω - μ ∨ ε / 2 ≤ μ - fe S w e ω) :=
        cubeProb_allZero_and_le _ H.hq _ _
    _ ≤ cubeProb q' (fun ω => ε / 2 ≤ fe S w e ω - μ) +
        cubeProb q' (fun ω => ε / 2 ≤ μ - fe S w e ω) := cubeProb_or_le _ hq' _ _
    _ ≤ _ := by linarith [hup.trans hmono, hlo.trans hmono]

end RoundHyp

end PartitionedTriangleAbsorption.Nibble
