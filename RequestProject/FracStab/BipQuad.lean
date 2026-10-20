/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.BipFinCount
public import RequestProject.FracStab.BipQuadLem
public import RequestProject.FracStab.BipClaim
public import RequestProject.FracStab.BipClass

@[expose] public section

/-!
# Lemma 9.5, second case: a nearly matched four part structure

Typical transversals and the bipartition they determine.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [DecidableEq V]

/-- All six pairs of the transversal `(x, y, w, z)` of the classes `i, j, k, l` are typical. -/
def Close6 (a : V → V → ℝ) (m : Fin 4 → Fin 4 → ℝ) (θ : ℝ) (i j k l : Fin 4) (x y w z : V) :
    Prop :=
  |a x y - m i j| ≤ θ ∧ |a x w - m i k| ≤ θ ∧ |a x z - m i l| ≤ θ ∧ |a y w - m j k| ≤ θ ∧
    |a y z - m j l| ≤ θ ∧ |a w z - m k l| ≤ θ

noncomputable instance (a : V → V → ℝ) (m : Fin 4 → Fin 4 → ℝ) (θ : ℝ) (i j k l : Fin 4)
    (x y w z : V) : Decidable (Close6 a m θ i j k l x y w z) := by
  unfold Close6; infer_instance

omit [DecidableEq V] in
lemma close_comm {a : V → V → ℝ} (hs : ∀ x y, a x y = a y x) {m : Fin 4 → Fin 4 → ℝ}
    (hm : ∀ i j, m i j = m j i) {θ : ℝ} (i j : Fin 4) (x y : V) :
    |a x y - m i j| ≤ θ ↔ |a y x - m j i| ≤ θ := by
  rw [hs x y, hm i j]

omit [DecidableEq V] in
/-- Bad transversals are few. -/
lemma bad6 {C : Finset V} {a : V → V → ℝ} {Vc : Fin 4 → Finset V} {m : Fin 4 → Fin 4 → ℝ}
    {θ : ℝ}
    (hfar : ∀ i j, i ≠ j → bsum (farI a (m i j) θ) (Vc i) (Vc j) ≤ θ * (C.card : ℝ) ^ 2)
    {i j k l : Fin 4} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) {A B D E : Finset V} (hA : A ⊆ Vc i) (hB : B ⊆ Vc j) (hD : D ⊆ Vc k)
    (hE : E ⊆ Vc l) (cA : (A.card : ℝ) ≤ C.card) (cB : (B.card : ℝ) ≤ C.card)
    (cD : (D.card : ℝ) ≤ C.card) (cE : (E.card : ℝ) ≤ C.card) :
    (((trans4 A B D E).filter fun z : (V × V) × (V × V) =>
      ¬ Close6 a m θ i j k l z.1.1 z.1.2 z.2.1 z.2.2).card : ℝ) ≤ 6 * θ * (C.card : ℝ) ^ 4 := by
  classical
  set c : ℝ := (C.card : ℝ) with hcdef
  have key : ∀ μ x y, farI a μ θ x y < 1 → |a x y - μ| ≤ θ := fun μ x y h => by
    unfold farI at h; split_ifs at h with hh
    · linarith
    · exact not_lt.1 hh
  have h := bad4 A B D E (farI a (m i j) θ) (farI a (m i k) θ) (farI a (m i l) θ)
    (farI a (m j k) θ) (farI a (m j l) θ) (farI a (m k l) θ)
    (fun x y => ⟨farI_nonneg _ _ _ _ _, farI_nonneg _ _ _ _ _, farI_nonneg _ _ _ _ _,
      farI_nonneg _ _ _ _ _, farI_nonneg _ _ _ _ _, farI_nonneg _ _ _ _ _⟩)
    (fun z => Close6 a m θ i j k l z.1.1 z.1.2 z.2.1 z.2.2)
    (by
      intro x y w t hG
      have n1 := farI_nonneg a (m i j) θ x y
      have n2 := farI_nonneg a (m i k) θ x w
      have n3 := farI_nonneg a (m i l) θ x t
      have n4 := farI_nonneg a (m j k) θ y w
      have n5 := farI_nonneg a (m j l) θ y t
      have n6 := farI_nonneg a (m k l) θ w t
      by_contra hlt
      push_neg at hlt
      exact hG ⟨key _ _ _ (by linarith), key _ _ _ (by linarith), key _ _ _ (by linarith),
        key _ _ _ (by linarith), key _ _ _ (by linarith), key _ _ _ (by linarith)⟩)
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have pp : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y → x ≤ c → y ≤ c → x * y ≤ c ^ 2 := by
    intro x y hx hy hxc hyc
    calc x * y ≤ c * c := mul_le_mul hxc hyc hy hc0
      _ = c ^ 2 := by ring
  have qq : ∀ (x y : ℝ) (i' j' : Fin 4), i' ≠ j' → ∀ X ⊆ Vc i', ∀ Y ⊆ Vc j',
      0 ≤ x → 0 ≤ y → x ≤ c → y ≤ c →
      x * y * bsum (farI a (m i' j') θ) X Y ≤ c ^ 2 * (θ * c ^ 2) :=
    fun x y i' j' hne X hX Y hY hx hy hxc hyc =>
      mul_le_mul (pp x y hx hy hxc hyc) ((bsum_farI_mono a _ θ hX hY).trans (hfar i' j' hne))
        (bsum_nonneg' (farI_nonneg a _ θ) _ _) (sq_nonneg c)
  have z := fun (P : Finset V) => (Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)
  have q1 := qq _ _ i j hij A hA B hB (z D) (z E) cD cE
  have q2 := qq _ _ i k hik A hA D hD (z B) (z E) cB cE
  have q3 := qq _ _ i l hil A hA E hE (z B) (z D) cB cD
  have q4 := qq _ _ j k hjk B hB D hD (z A) (z E) cA cE
  have q5 := qq _ _ j l hjl B hB E hE (z A) (z D) cA cD
  have q6 := qq _ _ k l hkl D hD E hE (z A) (z B) cA cB
  have : c ^ 2 * (θ * c ^ 2) = θ * c ^ 4 := by ring
  linarith

section orient

variable {a : V → V → ℝ} (hs : ∀ x y, a x y = a y x) {m : Fin 4 → Fin 4 → ℝ}
  (hm : ∀ i j, m i j = m j i) {θ : ℝ} {p q s t : Fin 4} {w1 w2 w3 w4 : V}
include hs hm

omit [DecidableEq V] in
lemma close6_O34 : Close6 a m θ s t p q w3 w4 w1 w2 ↔ Close6 a m θ p q s t w1 w2 w3 w4 := by
  have cc := fun i j x y => close_comm (θ := θ) hs hm i j x y
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h6, (cc _ _ _ _).1 h2, (cc _ _ _ _).1 h4, (cc _ _ _ _).1 h3, (cc _ _ _ _).1 h5, h1⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h6, (cc _ _ _ _).1 h2, (cc _ _ _ _).1 h4, (cc _ _ _ _).1 h3, (cc _ _ _ _).1 h5, h1⟩

omit [DecidableEq V] in
lemma close6_O21 : Close6 a m θ q p s t w2 w1 w3 w4 ↔ Close6 a m θ p q s t w1 w2 w3 w4 := by
  have cc := fun i j x y => close_comm (θ := θ) hs hm i j x y
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨(cc _ _ _ _).1 h1, h4, h5, h2, h3, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨(cc _ _ _ _).1 h1, h4, h5, h2, h3, h6⟩

omit [DecidableEq V] in
lemma close6_O31 : Close6 a m θ s p q t w3 w1 w2 w4 ↔ Close6 a m θ p q s t w1 w2 w3 w4 := by
  have cc := fun i j x y => close_comm (θ := θ) hs hm i j x y
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h4, (cc _ _ _ _).1 h1, h5, (cc _ _ _ _).1 h2, h6, h3⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨(cc _ _ _ _).1 h2, (cc _ _ _ _).1 h4, h6, h1, h3, h5⟩

omit [DecidableEq V] in
lemma close6_O24 : Close6 a m θ q t p s w2 w4 w1 w3 ↔ Close6 a m θ p q s t w1 w2 w3 w4 := by
  have cc := fun i j x y => close_comm (θ := θ) hs hm i j x y
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨(cc _ _ _ _).1 h2, h6, (cc _ _ _ _).1 h4, h3, h1, (cc _ _ _ _).1 h5⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h5, (cc _ _ _ _).1 h1, h4, (cc _ _ _ _).1 h3, (cc _ _ _ _).1 h6, h2⟩

end orient

/-- **The bipartition from a consistent family of typical transversals** (type I: the matching
`{w₁w₃, w₂w₄}` is normal, the bipartition is `V_q ∪ V_s | V_p ∪ V_t`). -/
theorem typeI_bip {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop} {du dv : V → ℝ}
    {Su Sv : Finset V} (L : LocFacts C a g U W A du dv Su Sv) {Vc : Fin 4 → Finset V}
    (P : Part4 C Vc) {m : Fin 4 → Fin 4 → ℝ} (hm : ∀ i j, m i j = m j i) {θ η : ℝ}
    (hfar : ∀ i j, i ≠ j → bsum (farI a (m i j) θ) (Vc i) (Vc j) ≤ θ * (C.card : ℝ) ^ 2)
    {p q s t : Fin 4} (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t)
    (hst : s ≠ t) {X1 X2 X3 X4 : Finset V} (x1 : X1 ⊆ Vc p) (x2 : X2 ⊆ Vc q) (x3 : X3 ⊆ Vc s)
    (x4 : X4 ⊆ Vc t) {Lb r : ℝ} (hLb : 0 < Lb) (l1 : Lb ≤ X1.card) (l2 : Lb ≤ X2.card)
    (l3 : Lb ≤ X3.card) (l4 : Lb ≤ X4.card) (hr0 : 0 ≤ r)
    (r1 : ((Vc p).card : ℝ) ≤ X1.card + 2 * r) (r2 : ((Vc q).card : ℝ) ≤ X2.card + 2 * r)
    (r3 : ((Vc s).card : ℝ) ≤ X3.card + 2 * r) (r4 : ((Vc t).card : ℝ) ≤ X4.card + 2 * r)
    (h3 h4 : V → Prop) [DecidablePred h3] [DecidablePred h4]
    (hE34 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Close6 a m θ p q s t w1 w2 w3 w4 →
      1 - η ≤ g w3 w4)
    (hE12 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Close6 a m θ p q s t w1 w2 w3 w4 →
      (w1 ∈ Su ∧ w2 ∈ Sv) ∨ 1 - η ≤ g w1 w2)
    (hT13 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Close6 a m θ p q s t w1 w2 w3 w4 →
      h3 w3 → 1 - η ≤ g w1 w3)
    (hT24 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Close6 a m θ p q s t w1 w2 w3 w4 →
      ¬ h4 w4 → 1 - η ≤ g w2 w4)
    {e3 e4 s0 : ℝ} (he3 : ((X3.filter fun x => ¬ h3 x).card : ℝ) ≤ e3)
    (he4 : ((X4.filter h4).card : ℝ) ≤ e4) (hS : min (Su.card : ℝ) Sv.card ≤ s0)
    (hbal : |((Vc q).card + (Vc s).card : ℝ) - C.card / 2| ≤ θ * C.card) :
    ∃ B ⊆ C, (1/4 - θ ^ 2) * (C.card : ℝ) ^ 2 - 4 * r * C.card -
      4 * (6 * θ * (C.card : ℝ) ^ 4 / Lb ^ 2) - e3 * C.card - e4 * C.card - s0 * C.card ≤
      (nrm g η B (C \ B) : ℝ) := by
  have hs := L.thin.symm
  set c : ℝ := (C.card : ℝ) with hcdef
  have hXc : ∀ {X : Finset V} {i : Fin 4}, X ⊆ Vc i → (X.card : ℝ) ≤ c := fun hX =>
    by rw [hcdef]; exact_mod_cast card_le_card (hX.trans (P.sub _))
  set B := Vc q ∪ Vc s with hBdef
  have hBC : B ⊆ C := union_subset (P.sub q) (P.sub s)
  refine ⟨B, hBC, ?_⟩
  -- blocks inside the bipartition
  have hL : X2 ∪ X3 ⊆ B := union_subset_union x2 x3
  have hR : X1 ∪ X4 ⊆ C \ B := by
    intro x hx
    rw [mem_sdiff, hBdef, mem_union, not_or]
    rcases mem_union.1 hx with h | h
    · exact ⟨P.sub p (x1 h), fun h' => disjoint_left.1 (P.disj p q hpq) (x1 h) h',
        fun h' => disjoint_left.1 (P.disj p s hps) (x1 h) h'⟩
    · exact ⟨P.sub t (x4 h), fun h' => disjoint_left.1 (P.disj t q hqt.symm) (x4 h) h',
        fun h' => disjoint_left.1 (P.disj t s hst.symm) (x4 h) h'⟩
  have d23 : Disjoint X2 X3 := disjoint_of_subset_left x2 (disjoint_of_subset_right x3
    (P.disj q s hqs))
  have d14 : Disjoint X1 X4 := disjoint_of_subset_left x1 (disjoint_of_subset_right x4
    (P.disj p t hpt))
  have hsplit : nrm g η (X2 ∪ X3) (X1 ∪ X4) =
      nrm g η X3 X4 + nrm g η X2 X1 + nrm g η X3 X1 + nrm g η X2 X4 := by
    rw [nrm_union_left g η d23, nrm_union_right g η _ d14, nrm_union_right g η _ d14]; ring
  have hmono := nrm_mono g η hL hR
  -- the bad transversals in the four orientations
  have hc1 := hXc x1; have hc2 := hXc x2; have hc3 := hXc x3; have hc4 := hXc x4
  have B34 := bad6 (C := C) hfar hst.symm.symm (Ne.symm hps) (Ne.symm hqs) (Ne.symm hpt)
    (Ne.symm hqt) hpq x3 x4 x1 x2 hc3 hc4 hc1 hc2
  have B21 := bad6 (C := C) hfar (Ne.symm hpq) hqs hqt hps hpt hst x2 x1 x3 x4 hc2 hc1 hc3 hc4
  have B31 := bad6 (C := C) hfar (Ne.symm hps) (Ne.symm hqs) hst hpq hpt hqt x3 x1 x2 x4 hc3
    hc1 hc2 hc4
  have B24 := bad6 (C := C) hfar hqt (Ne.symm hpq) hqs (Ne.symm hpt) (Ne.symm hst) hps x2 x4 x1
    x3 hc2 hc4 hc1 hc3
  rw [filter_congr fun z _ => not_congr (close6_O34 hs hm)] at B34
  rw [filter_congr fun z _ => not_congr (close6_O21 hs hm)] at B21
  rw [filter_congr fun z _ => not_congr (close6_O31 hs hm)] at B31
  rw [filter_congr fun z _ => not_congr (close6_O24 hs hm)] at B24
  have hcount := count_typeI g L.gsymm η (Su := Su) (Sv := Sv) (Close6 a m θ p q s t) h3 h4
    hLb l1 l2 l3 l4 hc1 hc2 B34 B21 B31 B24 hE34 hE12 hT13 hT24 he3 he4 hS
  -- the sizes
  have hsum : ((Vc p).card : ℝ) + (Vc q).card + (Vc s).card + (Vc t).card = c := by
    have := P.card_eq
    rw [Fin.sum_univ_four] at this
    rw [hcdef, this]
    exact sum_x_perm (x := fun i => ((Vc i).card : ℝ)) hpq hps hpt hqs hqt hst
  have y2 : (X2.card : ℝ) ≤ (Vc q).card := by exact_mod_cast card_le_card x2
  have y3 : (X3.card : ℝ) ≤ (Vc s).card := by exact_mod_cast card_le_card x3
  have y1 : (X1.card : ℝ) ≤ (Vc p).card := by exact_mod_cast card_le_card x1
  have y4 : (X4.card : ℝ) ≤ (Vc t).card := by exact_mod_cast card_le_card x4
  set xa : ℝ := (X2.card : ℝ) + X3.card
  set xb : ℝ := (X1.card : ℝ) + X4.card
  set A' : ℝ := ((Vc q).card : ℝ) + (Vc s).card
  set B' : ℝ := ((Vc p).card : ℝ) + (Vc t).card
  have hAB : A' + B' = c := by simp only [A', B']; linarith
  have hxa0 : 0 ≤ xa := by positivity
  have hB0 : 0 ≤ B' := by positivity
  have hprod : A' * B' - 4 * r * c ≤ xa * xb := by
    have e1 : xa - A' ≥ -(4 * r) := by simp only [xa, A']; linarith
    have e2 : xb - B' ≥ -(4 * r) := by simp only [xb, B']; linarith
    have e3' : xa ≤ A' := by simp only [xa, A']; linarith
    have k1 : xa * (-(4 * r)) ≤ xa * (xb - B') := mul_le_mul_of_nonneg_left e2 hxa0
    have k2 : B' * (-(4 * r)) ≤ B' * (xa - A') := mul_le_mul_of_nonneg_left e1 hB0
    have k3 : xa * (4 * r) ≤ A' * (4 * r) := mul_le_mul_of_nonneg_right e3' (by linarith)
    have k4 : r * c = r * A' + r * B' := by rw [← hAB]; ring
    linarith only [k1, k2, k3, k4]
  have hbal' : |A' - c / 2| ≤ θ * c := hbal
  have hAB2 : (1/4 - θ ^ 2) * c ^ 2 ≤ A' * B' := by
    have hB'' : B' = c - A' := by linarith
    rw [hB'']
    have := sq_abs (A' - c / 2)
    have h2 : |A' - c / 2| ^ 2 ≤ (θ * c) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbal' 2
    linarith only [this, h2]
  have hn : ((nrm g η (X2 ∪ X3) (X1 ∪ X4) : ℕ) : ℝ) ≤ (nrm g η B (C \ B) : ℝ) := by
    exact_mod_cast hmono
  rw [hsplit] at hn
  push_cast at hn
  linarith only [hn, hcount, hprod, hAB2]

end NashWilliams.Frac
