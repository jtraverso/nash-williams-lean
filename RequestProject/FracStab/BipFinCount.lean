/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.BipCount

@[expose] public section

/-!
# Lemma 9.5: counting normal pairs from typical transversals
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
lemma nrm_mono (g : V → V → ℝ) (η : ℝ) {P Q P' Q' : Finset V} (hP : P ⊆ P') (hQ : Q ⊆ Q') :
    nrm g η P Q ≤ nrm g η P' Q' :=
  card_le_card (filter_subset_filter _ (product_subset_product hP hQ))

lemma nrm_union_left (g : V → V → ℝ) (η : ℝ) {P P' : Finset V} (h : Disjoint P P')
    (Q : Finset V) : nrm g η (P ∪ P') Q = nrm g η P Q + nrm g η P' Q := by
  unfold nrm
  rw [union_product, filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (disjoint_product.2 (Or.inl h))

lemma nrm_union_right (g : V → V → ℝ) (η : ℝ) (P : Finset V) {Q Q' : Finset V}
    (h : Disjoint Q Q') : nrm g η P (Q ∪ Q') = nrm g η P Q + nrm g η P Q' := by
  unfold nrm
  rw [product_union, filter_union, card_union_of_disjoint]
  exact disjoint_filter_filter (disjoint_product.2 (Or.inr h))

/-- A block: pairs of `P × Q` that are not normal are poor or exceptional. -/
lemma block_count (g : V → V → ℝ) (η : ℝ) (P Q : Finset V) (R : Finset (V × V))
    (Good : (V × V) × (V × V) → Prop) [DecidablePred Good] (Ex : V × V → Prop) [DecidablePred Ex]
    (hgood : ∀ p ∈ P ×ˢ Q, ∀ r ∈ R, Good (p, r) → ¬ Ex p → 1 - η ≤ g p.1 p.2)
    {Bq Lb : ℝ} (hLb : 0 < Lb) (hR : Lb ^ 2 ≤ R.card)
    (hB : ((((P ×ˢ Q) ×ˢ R).filter fun z => ¬ Good z).card : ℝ) ≤ Bq) :
    (P.card : ℝ) * Q.card - Bq / Lb ^ 2 - ((P ×ˢ Q).filter Ex).card ≤ nrm g η P Q := by
  set poor := (P ×ˢ Q).filter fun p => ∀ r ∈ R, ¬ Good (p, r)
  have hpc := poor_count (P ×ˢ Q) R Good
  have hpoor : (poor.card : ℝ) ≤ Bq / Lb ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    have h0 : (0:ℝ) ≤ poor.card := Nat.cast_nonneg _
    calc (poor.card : ℝ) * Lb ^ 2 ≤ poor.card * R.card := mul_le_mul_of_nonneg_left hR h0
      _ ≤ _ := hpc
      _ ≤ Bq := hB
  have hsub : P ×ˢ Q ⊆ poor ∪ ((P ×ˢ Q).filter Ex) ∪
      ((P ×ˢ Q).filter fun p => 1 - η ≤ g p.1 p.2) := by
    intro p hp
    simp only [mem_union, mem_filter, poor]
    by_cases hx : Ex p
    · exact Or.inl (Or.inr ⟨hp, hx⟩)
    by_cases hpr : ∀ r ∈ R, ¬ Good (p, r)
    · exact Or.inl (Or.inl ⟨hp, hpr⟩)
    push_neg at hpr
    obtain ⟨r, hr, hg⟩ := hpr
    exact Or.inr ⟨hp, hgood p hp r hr hg hx⟩
  have := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  rw [card_product] at this
  have h' : ((P.card * Q.card : ℕ) : ℝ) ≤ poor.card + ((P ×ˢ Q).filter Ex).card +
      (nrm g η P Q : ℝ) := by exact_mod_cast this
  push_cast at h'
  linarith

/-- Pairs of `P × Q` with first coordinate in `S` (resp. second in `S'`). -/
lemma card_filter_mem_fst (P Q S : Finset V) :
    (((P ×ˢ Q).filter fun p => p.1 ∈ S).card : ℝ) ≤ S.card * Q.card := by
  have hsub : (P ×ˢ Q).filter (fun p => p.1 ∈ S) ⊆ S ×ˢ Q := by
    intro p hp; simp only [mem_filter, mem_product] at hp ⊢; exact ⟨hp.2, hp.1.2⟩
  have := card_le_card hsub; rw [card_product] at this; exact_mod_cast this

lemma card_filter_mem_snd (P Q S : Finset V) :
    (((P ×ˢ Q).filter fun p => p.2 ∈ S).card : ℝ) ≤ P.card * S.card := by
  have hsub : (P ×ˢ Q).filter (fun p => p.2 ∈ S) ⊆ P ×ˢ S := by
    intro p hp; simp only [mem_filter, mem_product] at hp ⊢; exact ⟨hp.1.1, hp.2⟩
  have := card_le_card hsub; rw [card_product] at this; exact_mod_cast this

/-- **Counting normal pairs** for a consistent family of typical transversals. -/
theorem count_typeI (g : V → V → ℝ) (hgs : ∀ x y, g x y = g y x) (η : ℝ)
    {X1 X2 X3 X4 Su Sv : Finset V} (Good : V → V → V → V → Prop)
    [∀ w1 w2 w3 w4, Decidable (Good w1 w2 w3 w4)]
    (h3 h4 : V → Prop) [DecidablePred h3] [DecidablePred h4] {Bq Lb c s0 e3 e4 : ℝ}
    (hLb : 0 < Lb) (l1 : Lb ≤ X1.card) (l2 : Lb ≤ X2.card) (l3 : Lb ≤ X3.card)
    (l4 : Lb ≤ X4.card) (u1 : (X1.card : ℝ) ≤ c) (u2 : (X2.card : ℝ) ≤ c)
    (hB34 : ((((X3 ×ˢ X4) ×ˢ (X1 ×ˢ X2)).filter
      fun z => ¬ Good z.2.1 z.2.2 z.1.1 z.1.2).card : ℝ) ≤ Bq)
    (hB21 : ((((X2 ×ˢ X1) ×ˢ (X3 ×ˢ X4)).filter
      fun z => ¬ Good z.1.2 z.1.1 z.2.1 z.2.2).card : ℝ) ≤ Bq)
    (hB31 : ((((X3 ×ˢ X1) ×ˢ (X2 ×ˢ X4)).filter
      fun z => ¬ Good z.1.2 z.2.1 z.1.1 z.2.2).card : ℝ) ≤ Bq)
    (hB24 : ((((X2 ×ˢ X4) ×ˢ (X1 ×ˢ X3)).filter
      fun z => ¬ Good z.2.1 z.1.1 z.2.2 z.1.2).card : ℝ) ≤ Bq)
    (hE34 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Good w1 w2 w3 w4 → 1 - η ≤ g w3 w4)
    (hE12 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Good w1 w2 w3 w4 →
      (w1 ∈ Su ∧ w2 ∈ Sv) ∨ 1 - η ≤ g w1 w2)
    (hT13 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Good w1 w2 w3 w4 → h3 w3 →
      1 - η ≤ g w1 w3)
    (hT24 : ∀ w1 ∈ X1, ∀ w2 ∈ X2, ∀ w3 ∈ X3, ∀ w4 ∈ X4, Good w1 w2 w3 w4 → ¬ h4 w4 →
      1 - η ≤ g w2 w4)
    (he3 : ((X3.filter fun x => ¬ h3 x).card : ℝ) ≤ e3) (he4 : ((X4.filter h4).card : ℝ) ≤ e4)
    (hS : min (Su.card : ℝ) Sv.card ≤ s0) :
    ((X2.card : ℝ) + X3.card) * (X1.card + X4.card) - 4 * (Bq / Lb ^ 2) - e3 * c - e4 * c -
      s0 * c ≤
      (nrm g η X3 X4 : ℝ) + nrm g η X2 X1 + nrm g η X3 X1 + nrm g η X2 X4 := by
  classical
  have hL2 : ∀ (P Q : Finset V), Lb ≤ P.card → Lb ≤ Q.card → Lb ^ 2 ≤ ((P ×ˢ Q).card : ℝ) := by
    intro P Q hP hQ
    rw [card_product]; push_cast
    rw [sq]; exact mul_le_mul hP hQ hLb.le (le_trans hLb.le hP)
  -- block (3,4)
  have k34 := block_count g η X3 X4 (X1 ×ˢ X2) (fun z => Good z.2.1 z.2.2 z.1.1 z.1.2)
    (fun _ => False)
    (by
      intro p hp r hr hG _
      simp only [mem_product] at hp hr
      exact hE34 _ hr.1 _ hr.2 _ hp.1 _ hp.2 hG)
    hLb (hL2 _ _ l1 l2) hB34
  -- block (2,1)
  have k21 := block_count g η X2 X1 (X3 ×ˢ X4) (fun z => Good z.1.2 z.1.1 z.2.1 z.2.2)
    (fun p => p.2 ∈ Su ∧ p.1 ∈ Sv)
    (by
      intro p hp r hr hG hx
      simp only [mem_product] at hp hr
      rcases hE12 _ hp.2 _ hp.1 _ hr.1 _ hr.2 hG with h | h
      · exact absurd h hx
      · rw [hgs]; exact h)
    hLb (hL2 _ _ l3 l4) hB21
  -- block (3,1)
  have k31 := block_count g η X3 X1 (X2 ×ˢ X4) (fun z => Good z.1.2 z.2.1 z.1.1 z.2.2)
    (fun p => ¬ h3 p.1)
    (by
      intro p hp r hr hG hx
      simp only [mem_product] at hp hr
      push_neg at hx
      rw [hgs]; exact hT13 _ hp.2 _ hr.1 _ hp.1 _ hr.2 hG hx)
    hLb (hL2 _ _ l2 l4) hB31
  -- block (2,4)
  have k24 := block_count g η X2 X4 (X1 ×ˢ X3) (fun z => Good z.2.1 z.1.1 z.2.2 z.1.2)
    (fun p => h4 p.2)
    (by
      intro p hp r hr hG hx
      simp only [mem_product] at hp hr
      exact hT24 _ hr.1 _ hp.1 _ hr.2 _ hp.2 hG hx)
    hLb (hL2 _ _ l1 l3) hB24
  -- the exceptional pairs
  have x34 : (((X3 ×ˢ X4).filter fun _ => False).card : ℝ) = 0 := by simp
  have x21 : (((X2 ×ˢ X1).filter fun p => p.2 ∈ Su ∧ p.1 ∈ Sv).card : ℝ) ≤ s0 * c := by
    have a1 := card_filter_mem_snd X2 X1 Su
    have a2 := card_filter_mem_fst X2 X1 Sv
    have hA' : (((X2 ×ˢ X1).filter fun p => p.2 ∈ Su ∧ p.1 ∈ Sv).card : ℝ) ≤
        ((X2 ×ˢ X1).filter fun p => p.2 ∈ Su).card := by
      exact_mod_cast card_le_card fun p hp => by
        simp only [mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.1⟩
    have hB' : (((X2 ×ˢ X1).filter fun p => p.2 ∈ Su ∧ p.1 ∈ Sv).card : ℝ) ≤
        ((X2 ×ˢ X1).filter fun p => p.1 ∈ Sv).card := by
      exact_mod_cast card_le_card fun p hp => by
        simp only [mem_filter] at hp ⊢; exact ⟨hp.1, hp.2.2⟩
    rcases le_total (Su.card : ℝ) Sv.card with h | h
    · rw [min_eq_left h] at hS
      calc _ ≤ _ := hA'
        _ ≤ (X2.card : ℝ) * Su.card := a1
        _ ≤ c * s0 := mul_le_mul u2 hS (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) u2)
        _ = s0 * c := by ring
    · rw [min_eq_right h] at hS
      calc _ ≤ _ := hB'
        _ ≤ (Sv.card : ℝ) * X1.card := a2
        _ ≤ s0 * c := mul_le_mul hS u1 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) hS)
  have x31 : (((X3 ×ˢ X1).filter fun p => ¬ h3 p.1).card : ℝ) ≤ e3 * c := by
    have hsub : (X3 ×ˢ X1).filter (fun p => ¬ h3 p.1) = (X3.filter fun x => ¬ h3 x) ×ˢ X1 := by
      ext p; simp only [mem_filter, mem_product]; tauto
    rw [hsub, card_product]; push_cast
    exact mul_le_mul he3 u1 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) he3)
  have x24 : (((X2 ×ˢ X4).filter fun p => h4 p.2).card : ℝ) ≤ e4 * c := by
    have hsub : (X2 ×ˢ X4).filter (fun p => h4 p.2) = X2 ×ˢ (X4.filter h4) := by
      ext p; simp only [mem_filter, mem_product]; tauto
    rw [hsub, card_product]; push_cast
    calc (X2.card : ℝ) * (X4.filter h4).card ≤ c * e4 :=
          mul_le_mul u2 he4 (Nat.cast_nonneg _) (le_trans (Nat.cast_nonneg _) u2)
      _ = e4 * c := by ring
  nlinarith

end NashWilliams.Frac
