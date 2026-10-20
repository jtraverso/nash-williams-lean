/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.BipQuad

@[expose] public section

/-!
# Lemma 9.5, second case: assembly
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
/-- Consistency of the heaviness types in the balanced case. -/
lemma consistency {X3 X4 : Finset V} (h : V → Prop) [DecidablePred h] {lam r' : ℝ}
    (hP : ((X3.filter h).card : ℝ) * (X4.filter h).card ≤ lam)
    (hN : ((X3.filter fun x => ¬ h x).card : ℝ) * (X4.filter fun x => ¬ h x).card ≤ lam)
    (hr : lam ≤ r' ^ 2) (hr0 : 0 < r') (h3 : 2 * r' < X3.card) (h4 : 2 * r' < X4.card) :
    (((X4.filter h).card : ℝ) ≤ r' ∧ ((X3.filter fun x => ¬ h x).card : ℝ) ≤ r') ∨
    (((X3.filter h).card : ℝ) ≤ r' ∧ ((X4.filter fun x => ¬ h x).card : ℝ) ≤ r') := by
  have e3 := card_filter_add_card_filter_not (s := X3) h
  have e4 := card_filter_add_card_filter_not (s := X4) h
  have e3' : ((X3.filter h).card : ℝ) + (X3.filter fun x => ¬ h x).card = X3.card := by
    exact_mod_cast e3
  have e4' : ((X4.filter h).card : ℝ) + (X4.filter fun x => ¬ h x).card = X4.card := by
    exact_mod_cast e4
  set P3 : ℝ := ((X3.filter h).card : ℝ)
  set N3 : ℝ := ((X3.filter fun x => ¬ h x).card : ℝ)
  set P4 : ℝ := ((X4.filter h).card : ℝ)
  set N4 : ℝ := ((X4.filter fun x => ¬ h x).card : ℝ)
  have p40 : 0 ≤ P4 := Nat.cast_nonneg _
  have n40 : 0 ≤ N4 := Nat.cast_nonneg _
  -- if one factor exceeds `r'`, the other is below `r'`
  have small : ∀ x y : ℝ, 0 ≤ y → x * y ≤ lam → r' < x → y < r' := by
    intro x y hy hxy hx
    by_contra hcon; push_neg at hcon
    have : r' * r' < x * y := by
      calc r' * r' < x * r' := mul_lt_mul_of_pos_right hx hr0
        _ ≤ x * y := mul_le_mul_of_nonneg_left hcon (by linarith)
    nlinarith
  by_cases hp3 : P3 ≤ r'
  · right
    refine ⟨hp3, (small N3 N4 n40 hN (by linarith)).le⟩
  · left
    push_neg at hp3
    have hp4 := small P3 P4 p40 hP hp3
    refine ⟨hp4.le, ?_⟩
    by_contra hn3; push_neg at hn3
    have hn4 := small N3 N4 n40 hN hn3
    linarith

omit [DecidableEq V] in
lemma close6_swap34 {a : V → V → ℝ} (hs : ∀ x y, a x y = a y x) {m : Fin 4 → Fin 4 → ℝ}
    (hm : ∀ i j, m i j = m j i) {θ : ℝ} {p q s t : Fin 4} {w1 w2 w3 w4 : V} :
    Close6 a m θ p q t s w1 w2 w3 w4 ↔ Close6 a m θ p q s t w1 w2 w4 w3 := by
  have cc := fun i j x y => close_comm (θ := θ) hs hm i j x y
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h3, h2, h5, h4, (cc _ _ _ _).1 h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h3, h2, h5, h4, (cc _ _ _ _).1 h6⟩

set_option maxHeartbeats 1000000 in
/-- **The four part case of Lemma 9.5.** -/
theorem quad_case {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop} {du dv : V → ℝ}
    {Su Sv : Finset V} (L : LocFacts C a g U W A du dv Su Sv) [DecidablePred U]
    [DecidablePred W] [DecidablePred A] {κ τ θ β s0 η : ℝ} (hQ : QuadStruct C a κ τ θ)
    (hc : 0 < (C.card : ℝ)) (hθ0 : 0 < θ) (hβ0 : 0 < β) (hκ0 : 0 < κ) (hθβ : θ ≤ β ^ 2)
    (h8β : 8 * β ≤ κ) (h20β : 20 * β < κ ^ 2) (hθτ : θ < τ)
    (hζ1 : 3 * θ + 48 * θ / κ ^ 4 + 3 * θ < 1/6)
    (hζτ : 3 * θ + 48 * θ / κ ^ 4 + τ ≤ 1/2) (hθτ' : 4 * θ + τ ≤ 1/2)
    (hη : 6 * (3 * θ + 48 * θ / κ ^ 4) + 42 * θ ≤ η)
    (hS : min (Su.card : ℝ) Sv.card ≤ s0) :
    ∃ B ⊆ C, (1/4 - (θ ^ 2 + 8 * β + 96 * θ / κ ^ 2 + 10 * β / κ)) * (C.card : ℝ) ^ 2 -
      s0 * C.card ≤ (nrm g η B (C \ B) : ℝ) := by
  classical
  obtain ⟨Vc, m, hsub, hdisj, hcov, hsize, hm, hmr, hmatch, htri, hbal, hconc⟩ := hQ
  have P : Part4 C Vc := ⟨hsub, hdisj, hcov⟩
  have hs := L.thin.symm
  set c : ℝ := (C.card : ℝ) with hcdef
  set ζ : ℝ := 3 * θ + 48 * θ / κ ^ 4 with hζdef
  have hζ0 : 0 ≤ ζ := by positivity
  have hfar : ∀ i j, i ≠ j → bsum (farI a (m i j) θ) (Vc i) (Vc j) ≤ θ * c ^ 2 := by
    intro i j hij; rw [bsum_farI]; exact hconc i j hij
  -- the classification
  set r : ℝ := 2 * β * c with hrdef
  have hr0 : 0 ≤ r := by positivity
  obtain ⟨p, q, s, t, hpq, hps, hpt, hqs, hqt, hst, r1, r2, r3, r4⟩ :=
    classify L P (m := m) (τ := τ) (θ := θ) (r := r) hsize (fun i j hij => (hmr i j hij).1) hfar
      hθ0.le hθτ hr0 (by rw [hrdef]; nlinarith) (by rw [hrdef]; nlinarith)
  set X1 := (Vc p).filter U with hX1
  set X2 := (Vc q).filter W with hX2
  set X3 := (Vc s).filter A with hX3
  set X4 := (Vc t).filter A with hX4
  set Lb : ℝ := κ * c / 2 with hLbdef
  have hLb : 0 < Lb := by positivity
  have hXL : ∀ {i : Fin 4} {X : Finset V}, ((Vc i).card : ℝ) ≤ X.card + 2 * r → Lb ≤ X.card :=
    fun {i} {X} h => by have := hsize i; rw [hrdef] at h; rw [hLbdef]; nlinarith
  have l1 := hXL r1; have l2 := hXL r2; have l3 := hXL r3; have l4 := hXL r4
  have x1 : X1 ⊆ Vc p := filter_subset _ _
  have x2 : X2 ⊆ Vc q := filter_subset _ _
  have x3 : X3 ⊆ Vc s := filter_subset _ _
  have x4 : X4 ⊆ Vc t := filter_subset _ _
  have hXc : ∀ {X : Finset V} {i : Fin 4}, X ⊆ Vc i → (X.card : ℝ) ≤ c := fun hX =>
    by rw [hcdef]; exact_mod_cast card_le_card (hX.trans (P.sub _))
  -- Claim 9.5.6
  have hclaim : m p s + m q s ≤ 1 + ζ := by
    have h := claim956 L (x1.trans (P.sub p)) (x2.trans (P.sub q)) (x3.trans (P.sub s))
      (x4.trans (P.sub t)) (fun x hx => (mem_filter.1 hx).2) (fun x hx => (mem_filter.1 hx).2)
      (fun x hx => (mem_filter.1 hx).2) (fun x hx => (mem_filter.1 hx).2)
      (M13 := m p s) (M23 := m q s) (M14 := m p t) (M24 := m q t) (M34 := m s t)
      hθ0.le (by linarith [(hmr s t hst).1])
      (by linarith [(hmr p s hps).2]) (by linarith [(hmr q s hqs).2])
      (by linarith [(hmr p t hpt).2]) (by linarith [(hmr q t hqt).2])
      ((bsum_farI_mono _ _ _ x1 x3).trans (hfar p s hps))
      ((bsum_farI_mono _ _ _ x2 x3).trans (hfar q s hqs))
      ((bsum_farI_mono _ _ _ x1 x4).trans (hfar p t hpt))
      ((bsum_farI_mono _ _ _ x2 x4).trans (hfar q t hqt))
      ((bsum_farI_mono _ _ _ x3 x4).trans (hfar s t hst)) (hXc x1) (hXc x2) (hXc x3) (hXc x4)
    have mt1 := (abs_le.1 (hmatch q t p s hqt (Ne.symm hpq) hqs (Ne.symm hpt) hst.symm hps)).1
    have mt2 := (abs_le.1 (hmatch p t q s hpt hpq hps (Ne.symm hqt) hst.symm hqs)).1
    have hN : Lb ^ 4 ≤ (X1.card : ℝ) * X2.card * X3.card * X4.card := by
      have a1 : Lb ^ 2 ≤ (X1.card : ℝ) * X2.card := by
        rw [sq]; exact mul_le_mul l1 l2 hLb.le (le_trans hLb.le l1)
      have a2 : Lb ^ 2 ≤ (X3.card : ℝ) * X4.card := by
        rw [sq]; exact mul_le_mul l3 l4 hLb.le (le_trans hLb.le l3)
      calc Lb ^ 4 = Lb ^ 2 * Lb ^ 2 := by ring
        _ ≤ ((X1.card : ℝ) * X2.card) * (X3.card * X4.card) :=
            mul_le_mul a1 a2 (by positivity) (by positivity)
        _ = _ := by ring
    have hL4 : Lb ^ 4 = κ ^ 4 * c ^ 4 / 16 := by rw [hLbdef]; ring
    have key : m p s + m q s + m p t + m q t - 2 - 4 * θ ≤ 96 * θ / κ ^ 4 := by
      by_contra hcon; push_neg at hcon
      have hpos : 0 < m p s + m q s + m p t + m q t - 2 - 4 * θ := by
        have : 0 < 96 * θ / κ ^ 4 := by positivity
        linarith
      have h1 : (m p s + m q s + m p t + m q t - 2 - 4 * θ) * Lb ^ 4 ≤ 6 * (θ * c ^ 2) * c ^ 2 :=
        le_trans (mul_le_mul_of_nonneg_left hN hpos.le) h
      rw [hL4] at h1
      have h2 : 96 * θ / κ ^ 4 * (κ ^ 4 * c ^ 4 / 16) = 6 * (θ * c ^ 2) * c ^ 2 := by
        field_simp; ring
      have h3 : 96 * θ / κ ^ 4 * (κ ^ 4 * c ^ 4 / 16) <
          (m p s + m q s + m p t + m q t - 2 - 4 * θ) * (κ ^ 4 * c ^ 4 / 16) :=
        mul_lt_mul_of_pos_right hcon (by positivity)
      linarith
    have e : 96 * θ / κ ^ 4 = 2 * (48 * θ / κ ^ 4) := by ring
    rw [hζdef]; linarith
  -- facts about typical transversals
  have hmr1 : ∀ i j, i ≠ j → m i j ≤ 1 := fun i j h => (hmr i j h).2
  have hT : ∀ {w1 w2 w3 w4 : V}, w1 ∈ X1 → w2 ∈ X2 → w3 ∈ X3 → w4 ∈ X4 →
      QuadT C U W A w1 w2 w3 w4 := fun h1 h2 h3 h4 =>
    ⟨P.sub p (x1 h1), P.sub q (x2 h2), P.sub s (x3 h3), P.sub t (x4 h4), (mem_filter.1 h1).2,
      (mem_filter.1 h2).2, (mem_filter.1 h3).2, (mem_filter.1 h4).2⟩
  have htpqs := (abs_le.1 (htri p q s hpq hps hqs)).1
  have hH : ∀ {w1 w2 w3 w4 : V}, Close6 a m θ p q s t w1 w2 w3 w4 →
      QuadH a w1 w2 w3 w4 (m p q) (m p s) (m p t) (m q s) (m q t) (m s t) θ ζ := fun hG =>
    ⟨hG.1, hG.2.1, hG.2.2.1, hG.2.2.2.1, hG.2.2.2.2.1, hG.2.2.2.2.2, by linarith,
      by linarith [hmr1 p q hpq], hclaim,
      hmatch q t p s hqt (Ne.symm hpq) hqs (Ne.symm hpt) hst.symm hps,
      hmatch p t q s hpt hpq hps (Ne.symm hqt) hst.symm hqs,
      hmatch s t p q hst (Ne.symm hps) (Ne.symm hqs) (Ne.symm hpt) (Ne.symm hqt) hpq⟩
  have he0 : ζ + 3 * θ ≤ 1/6 := by rw [hζdef]; linarith
  have hE : ∀ {w1 w2 w3 w4 : V}, w1 ∈ X1 → w2 ∈ X2 → w3 ∈ X3 → w4 ∈ X4 →
      Close6 a m θ p q s t w1 w2 w3 w4 →
      1 - 6 * (ζ + 3 * θ) ≤ g w3 w4 ∧ ((w1 ∈ Su ∧ w2 ∈ Sv) ∨ 1 - 6 * (ζ + 3 * θ) ≤ g w1 w2) :=
    fun h1 h2 h3 h4 hG => quad_E L (hT h1 h2 h3 h4) (hH hG) hθ0.le hζ0 he0
  have hη1 : 1 - η ≤ 1 - 6 * (ζ + 3 * θ) := by rw [hζdef] at *; linarith
  have hη2 : 1 - η ≤ 1 - 10 * θ := by rw [hζdef] at *; linarith
  have hη3 : 1 - η ≤ 1 - (4 * (3 * θ) + 12 * θ) := by rw [hζdef] at *; linarith
  have hg34 : ∀ {w1 w2 w3 w4 : V}, w1 ∈ X1 → w2 ∈ X2 → w3 ∈ X3 → w4 ∈ X4 →
      Close6 a m θ p q s t w1 w2 w3 w4 → 0 < g w3 w4 := fun h1 h2 h3 h4 hG => by
    have := (hE h1 h2 h3 h4 hG).1; rw [hζdef] at *; linarith
  -- converting the bound of `typeI_bip`
  set r' : ℝ := 5 * β * c / κ with hr'def
  have hr'0 : 0 < r' := by positivity
  have conv : ∀ N e3 e4 : ℝ, e3 ≤ r' → e4 ≤ r' →
      (1/4 - θ ^ 2) * c ^ 2 - 4 * r * c - 4 * (6 * θ * c ^ 4 / Lb ^ 2) - e3 * c - e4 * c -
        s0 * c ≤ N →
      (1/4 - (θ ^ 2 + 8 * β + 96 * θ / κ ^ 2 + 10 * β / κ)) * c ^ 2 - s0 * c ≤ N := by
    intro N e3 e4 h3 h4 hN
    have k1 : 4 * (6 * θ * c ^ 4 / Lb ^ 2) = 96 * θ / κ ^ 2 * c ^ 2 := by
      rw [hLbdef]; field_simp; ring
    have k2 : e3 * c ≤ r' * c := mul_le_mul_of_nonneg_right h3 hc.le
    have k3 : e4 * c ≤ r' * c := mul_le_mul_of_nonneg_right h4 hc.le
    have k4 : r' * c = 5 * β / κ * c ^ 2 := by rw [hr'def]; ring
    have k5 : 4 * r * c = 8 * β * c ^ 2 := by rw [hrdef]; ring
    have k6 : (1/4 - (θ ^ 2 + 8 * β + 96 * θ / κ ^ 2 + 10 * β / κ)) * c ^ 2 =
        (1/4 - θ ^ 2) * c ^ 2 - 8 * β * c ^ 2 - 96 * θ / κ ^ 2 * c ^ 2 -
          2 * (5 * β / κ * c ^ 2) := by ring
    linarith only [hN, k1, k2, k3, k4, k5, k6]
  have hbal' : ∀ i j k l : Fin 4, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      m i j ≤ 1 - τ → |((Vc i).card + (Vc j).card : ℝ) - c / 2| ≤ θ * c := hbal
  have mt1 := abs_le.1 (hmatch q t p s hqt (Ne.symm hpq) hqs (Ne.symm hpt) hst.symm hps)
  have hb2 : 2 * θ ≤ 3 * θ := by linarith only [hθ0]
  by_cases hc1 : 1/2 + 3 * θ < m p s
  · -- the matching `{w₁w₃, w₂w₄}`
    obtain ⟨B, hB, hN⟩ := typeI_bip L P hm hfar hpq hps hpt hqs hqt hst x1 x2 x3 x4 hLb l1 l2
      l3 l4 hr0 r1 r2 r3 r4 (fun _ => True) (fun _ => False) (e3 := 0) (e4 := 0) (s0 := s0)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => le_trans hη1 (hE h1 h2 h3 h4 hG).1)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => by
        rcases (hE h1 h2 h3 h4 hG).2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans hη1 h))
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG _ => le_trans hη2
        (quad_case1 L (hT h1 h2 h3 h4) (hH hG) hb2 hc1 (hg34 h1 h2 h3 h4 hG)).1)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG _ => le_trans hη2
        (quad_case1 L (hT h1 h2 h3 h4) (hH hG) hb2 hc1 (hg34 h1 h2 h3 h4 hG)).2)
      (by simp) (by simp) hS
      (hbal' q s p t hqs (Ne.symm hpq) hqt (Ne.symm hps) hst hpt
        (by linarith only [hclaim, hc1, hζτ, hθ0]))
    exact ⟨B, hB, conv _ 0 0 hr'0.le hr'0.le hN⟩
  by_cases hc2 : 1/2 + 3 * θ < m q s
  · -- the matching `{w₂w₃, w₁w₄}`: relabel `s ↔ t`
    have sw : ∀ {w1 w2 w3 w4 : V}, Close6 a m θ p q t s w1 w2 w3 w4 →
        Close6 a m θ p q s t w1 w2 w4 w3 := fun hG => (close6_swap34 hs hm).1 hG
    obtain ⟨B, hB, hN⟩ := typeI_bip L P hm hfar hpq hpt hps hqt hqs hst.symm x1 x2 x4 x3 hLb l1
      l2 l4 l3 hr0 r1 r2 r4 r3 (fun _ => True) (fun _ => False) (e3 := 0) (e4 := 0) (s0 := s0)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => by
        rw [L.gsymm]; exact le_trans hη1 (hE h1 h2 h4 h3 (sw hG)).1)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => by
        rcases (hE h1 h2 h4 h3 (sw hG)).2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans hη1 h))
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG _ => le_trans hη2
        (quad_case2 L (hT h1 h2 h4 h3) (hH (sw hG)) hb2 hc2
          (hg34 h1 h2 h4 h3 (sw hG))).2)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG _ => le_trans hη2
        (quad_case2 L (hT h1 h2 h4 h3) (hH (sw hG)) hb2 hc2
          (hg34 h1 h2 h4 h3 (sw hG))).1)
      (by simp) (by simp) hS
      (hbal' q t p s hqt (Ne.symm hpq) hqs (Ne.symm hpt) hst.symm hps
        (by linarith only [hclaim, hc2, hζτ, hθ0, mt1.2]))
    exact ⟨B, hB, conv _ 0 0 hr'0.le hr'0.le hN⟩
  -- the balanced case
  push_neg at hc1 hc2
  have hκ4 : 0 ≤ 48 * θ / κ ^ 4 := by positivity
  have hsmall : 4 * (3 * θ) + 12 * θ < 1 := by linarith only [hζ1, hθ0, hκ4]
  have hmid : ∀ {w1 w2 w3 w4 : V}, w1 ∈ X1 → w2 ∈ X2 → w3 ∈ X3 → w4 ∈ X4 →
      Close6 a m θ p q s t w1 w2 w3 w4 →
      (1 - (4 * (3 * θ) + 12 * θ) ≤ g w1 w3 ∧ 1 - (4 * (3 * θ) + 12 * θ) ≤ g w2 w4 ∧
        1 - (2 * (3 * θ) + 6 * θ) ≤ du w3 ∧ 1 - (2 * (3 * θ) + 6 * θ) ≤ dv w4) ∨
      (1 - (4 * (3 * θ) + 12 * θ) ≤ g w2 w3 ∧ 1 - (4 * (3 * θ) + 12 * θ) ≤ g w1 w4 ∧
        1 - (2 * (3 * θ) + 6 * θ) ≤ dv w3 ∧ 1 - (2 * (3 * θ) + 6 * θ) ≤ du w4) :=
    fun h1 h2 h3 h4 hG => quad_case_mid L (hT h1 h2 h3 h4) (hH hG) hc1 hc2
      (hg34 h1 h2 h3 h4 hG) hsmall
  set hh : V → Prop := fun w => 1 - (2 * (3 * θ) + 6 * θ) ≤ du w with hhdef
  have hξ : 1 < 2 * (1 - (2 * (3 * θ) + 6 * θ)) := by linarith only [hsmall]
  have hdC : ∀ {w : V} {i : Fin 4} {X : Finset V}, X ⊆ Vc i → w ∈ X → du w + dv w = 1 :=
    fun hX hw => L.dsum _ (P.sub _ (hX hw))
  -- all transversals through two heavy (resp. two light) acute vertices are atypical
  have hcnt : ∀ P3 P4 : Finset V, P3 ⊆ X3 → P4 ⊆ X4 →
      (∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ P3, ∀ w4 ∈ P4, ¬ Close6 a m θ p q s t w1 w2 w3 w4) →
      (P3.card : ℝ) * P4.card ≤ 6 * θ * c ^ 4 / Lb ^ 2 := by
    intro P3 P4 hP3 hP4 hbad
    have hsub : (X1 ×ˢ X2) ×ˢ (P3 ×ˢ P4) ⊆ (trans4 X1 X2 X3 X4).filter
        (fun z : (V × V) × (V × V) => ¬ Close6 a m θ p q s t z.1.1 z.1.2 z.2.1 z.2.2) := by
      intro z hz
      simp only [mem_product] at hz
      simp only [trans4, mem_filter, mem_product]
      exact ⟨⟨⟨hz.1.1, hz.1.2⟩, hP3 hz.2.1, hP4 hz.2.2⟩,
        hbad _ hz.1.1 _ hz.1.2 _ hz.2.1 _ hz.2.2⟩
    have hb := bad6 (C := C) hfar hpq hps hpt hqs hqt hst x1 x2 x3 x4 (hXc x1) (hXc x2)
      (hXc x3) (hXc x4)
    have hc' : (((X1 ×ˢ X2) ×ˢ (P3 ×ˢ P4)).card : ℝ) ≤ 6 * θ * c ^ 4 :=
      le_trans (by exact_mod_cast card_le_card hsub) hb
    simp only [card_product] at hc'
    push_cast at hc'
    have hL2 : Lb ^ 2 ≤ (X1.card : ℝ) * X2.card := by
      rw [sq]; exact mul_le_mul l1 l2 hLb.le (le_trans hLb.le l1)
    rw [le_div_iff₀ (by positivity)]
    have h0 : (0:ℝ) ≤ P3.card * P4.card := by positivity
    calc (P3.card : ℝ) * P4.card * Lb ^ 2 ≤ P3.card * P4.card * (X1.card * X2.card) :=
          mul_le_mul_of_nonneg_left hL2 h0
      _ = X1.card * X2.card * (P3.card * P4.card) := by ring
      _ ≤ 6 * θ * c ^ 4 := hc'
  have hPP := hcnt (X3.filter hh) (X4.filter hh) (filter_subset _ _) (filter_subset _ _) (by
    intro w1 h1 w2 h2 w3 h3 w4 h4 hG
    rw [mem_filter] at h3 h4
    rcases hmid h1 h2 h3.1 h4.1 hG with ⟨-, -, -, k⟩ | ⟨-, -, k, -⟩
    · have := hdC x4 h4.1; linarith only [this, k, h4.2, hξ]
    · have := hdC x3 h3.1; linarith only [this, k, h3.2, hξ])
  have hNN := hcnt (X3.filter fun w => ¬ hh w) (X4.filter fun w => ¬ hh w) (filter_subset _ _)
    (filter_subset _ _) (by
    intro w1 h1 w2 h2 w3 h3 w4 h4 hG
    rw [mem_filter] at h3 h4
    rcases hmid h1 h2 h3.1 h4.1 hG with ⟨-, -, k, -⟩ | ⟨-, -, -, k⟩
    · exact h3.2 k
    · exact h4.2 k)
  have hlam : 6 * θ * c ^ 4 / Lb ^ 2 ≤ r' ^ 2 := by
    have e1 : 6 * θ * c ^ 4 / Lb ^ 2 = 24 * θ * c ^ 2 / κ ^ 2 := by rw [hLbdef]; field_simp; ring
    have e2 : r' ^ 2 = 25 * β ^ 2 * c ^ 2 / κ ^ 2 := by rw [hr'def]; field_simp; ring
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have h2r : 2 * r' < Lb := by
    rw [hr'def, hLbdef]
    rw [show 2 * (5 * β * c / κ) = 10 * β * c / κ by ring, div_lt_iff₀ hκ0]
    nlinarith
  rcases consistency hh hPP hNN hlam hr'0 (by linarith only [h2r, l3]) (by linarith only [h2r, l4])
    with ⟨e4, e3⟩ | ⟨e3, e4⟩
  · -- the matching `{w₁w₃, w₂w₄}` for almost all transversals
    obtain ⟨B, hB, hN⟩ := typeI_bip L P hm hfar hpq hps hpt hqs hqt hst x1 x2 x3 x4 hLb l1 l2
      l3 l4 hr0 r1 r2 r3 r4 hh hh (s0 := s0)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => le_trans hη1 (hE h1 h2 h3 h4 hG).1)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => by
        rcases (hE h1 h2 h3 h4 hG).2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans hη1 h))
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG k => by
        rcases hmid h1 h2 h3 h4 hG with ⟨j, -, -, -⟩ | ⟨-, -, j, -⟩
        · exact le_trans hη3 j
        · have := hdC x3 h3
          exact absurd hξ (not_lt.2 (by linarith only [this, k, j])))
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG k => by
        rcases hmid h1 h2 h3 h4 hG with ⟨-, j, -, -⟩ | ⟨-, -, -, j⟩
        · exact le_trans hη3 j
        · exact absurd j k)
      e3 e4 hS
      (hbal' q s p t hqs (Ne.symm hpq) hqt (Ne.symm hps) hst hpt
        (by linarith only [hc2, hθτ', hθ0]))
    exact ⟨B, hB, conv _ _ _ le_rfl le_rfl hN⟩
  · -- the matching `{w₂w₃, w₁w₄}` for almost all transversals: relabel `s ↔ t`
    have sw : ∀ {w1 w2 w3 w4 : V}, Close6 a m θ p q t s w1 w2 w3 w4 →
        Close6 a m θ p q s t w1 w2 w4 w3 := fun hG => (close6_swap34 hs hm).1 hG
    obtain ⟨B, hB, hN⟩ := typeI_bip L P hm hfar hpq hpt hps hqt hqs hst.symm x1 x2 x4 x3 hLb l1
      l2 l4 l3 hr0 r1 r2 r4 r3 hh hh (s0 := s0)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => by
        rw [L.gsymm]; exact le_trans hη1 (hE h1 h2 h4 h3 (sw hG)).1)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG => by
        rcases (hE h1 h2 h4 h3 (sw hG)).2 with h | h
        · exact Or.inl h
        · exact Or.inr (le_trans hη1 h))
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG k => by
        rcases hmid h1 h2 h4 h3 (sw hG) with ⟨-, -, -, j⟩ | ⟨-, j, -, -⟩
        · have := hdC x4 h3
          exact absurd hξ (not_lt.2 (by linarith only [this, k, j]))
        · exact le_trans hη3 j)
      (fun w1 h1 w2 h2 w3 h3 w4 h4 hG k => by
        rcases hmid h1 h2 h4 h3 (sw hG) with ⟨-, -, j, -⟩ | ⟨j, -, -, -⟩
        · exact absurd j k
        · exact le_trans hη3 j)
      e4 e3 hS
      (hbal' q t p s hqt (Ne.symm hpq) hqs (Ne.symm hpt) hst.symm hps
        (by linarith only [hc1, hθτ', mt1.2, hθ0]))
    exact ⟨B, hB, conv _ _ _ le_rfl le_rfl hN⟩

end NashWilliams.Frac
