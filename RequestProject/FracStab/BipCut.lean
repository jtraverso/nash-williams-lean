/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.BipAbs

/-!
# Lemma 9.5, first case: the value weighting is close to a cut
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [DecidableEq V]

/-- Pairs in `P × Q` meeting `S` in a fixed coordinate. -/
lemma card_pairs_meet (P Q S : Finset V) :
    (((P ×ˢ Q).filter fun p => p.1 ∈ S ∨ p.2 ∈ S).card : ℝ) ≤
      S.card * Q.card + P.card * S.card := by
  have hsub : (P ×ˢ Q).filter (fun p => p.1 ∈ S ∨ p.2 ∈ S) ⊆ (S ×ˢ Q) ∪ (P ×ˢ S) := by
    intro p hp
    simp only [mem_filter, mem_product, mem_union] at hp ⊢
    rcases hp.2 with h | h
    · exact Or.inl ⟨h, hp.1.2⟩
    · exact Or.inr ⟨hp.1.1, h⟩
  have := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_product, card_product] at this
  exact_mod_cast this

/-- `|B| |C \ B| ≥ (1/4 - δ²) |C|²` for an almost balanced bipartition. -/
lemma card_mul_compl_ge {C B : Finset V} (hB : B ⊆ C) {δ : ℝ}
    (h1 : (B.card : ℝ) ≤ (1/2 + δ) * C.card) (h2 : ((C \ B).card : ℝ) ≤ (1/2 + δ) * C.card) :
    (1/4 - δ^2) * (C.card : ℝ) ^ 2 ≤ (B.card : ℝ) * (C \ B).card := by
  have hc : ((C \ B).card : ℝ) = C.card - B.card := by
    rw [card_sdiff_of_subset hB, Nat.cast_sub (card_le_card hB)]
  rw [hc] at h2 ⊢
  nlinarith [sq_nonneg ((B.card : ℝ) - C.card / 2)]

/-- **The cut case of Lemma 9.5.** -/
theorem cut_case {C : Finset V} {a g : V → V → ℝ} {U W A : V → Prop} {du dv : V → ℝ}
    {Su Sv : Finset V} (L : LocFacts C a g U W A du dv Su Sv) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ 1/6) (hC : CutStruct C a δ) {s0 : ℝ}
    (hS : min (Su.card : ℝ) Sv.card ≤ s0) :
    ∃ B ⊆ C, (1/4 - δ^2 - δ) * (C.card : ℝ) ^ 2 - 2 * s0 * C.card ≤
      (nrm g (6 * δ) B (C \ B) : ℝ) := by
  obtain ⟨B, hB, h1, h2, h3⟩ := hC
  refine ⟨B, hB, ?_⟩
  -- the smaller of `Su, Sv`
  obtain ⟨S, hSs, hST⟩ : ∃ S : Finset V, (S.card : ℝ) ≤ s0 ∧
      ∀ x y, ((x ∈ Su ∧ y ∈ Sv) ∨ (x ∈ Sv ∧ y ∈ Su)) → x ∈ S ∨ y ∈ S := by
    rcases le_total (Su.card : ℝ) Sv.card with h | h
    · refine ⟨Su, by rw [min_eq_left h] at hS; exact hS, fun x y hxy => ?_⟩
      rcases hxy with h' | h'
      · exact Or.inl h'.1
      · exact Or.inr h'.2
    · refine ⟨Sv, by rw [min_eq_right h] at hS; exact hS, fun x y hxy => ?_⟩
      rcases hxy with h' | h'
      · exact Or.inr h'.2
      · exact Or.inl h'.1
  set P := B ×ˢ (C \ B)
  have hcover : P ⊆ (P.filter fun p => a p.1 p.2 < 1 - δ) ∪
      (P.filter fun p => p.1 ∈ S ∨ p.2 ∈ S) ∪ (P.filter fun p => 1 - 6 * δ ≤ g p.1 p.2) := by
    intro p hp
    simp only [mem_union, mem_filter]
    by_cases hlt : a p.1 p.2 < 1 - δ
    · exact Or.inl (Or.inl ⟨hp, hlt⟩)
    push_neg at hlt
    have hp' := mem_product.1 hp
    have hx : p.1 ∈ C := hB hp'.1
    have hy : p.2 ∈ C := (mem_sdiff.1 hp'.2).1
    rcases L.F7 _ hx _ hy δ hδ0 hδ hlt with h | h | h
    · exact Or.inl (Or.inr ⟨hp, hST _ _ (Or.inl h)⟩)
    · exact Or.inl (Or.inr ⟨hp, hST _ _ (Or.inr h)⟩)
    · exact Or.inr ⟨hp, h⟩
  have hcard := (card_le_card hcover).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have hcR : (P.card : ℝ) ≤ ((P.filter fun p => a p.1 p.2 < 1 - δ).card : ℝ) +
      ((P.filter fun p => p.1 ∈ S ∨ p.2 ∈ S).card : ℝ) + (nrm g (6 * δ) B (C \ B) : ℝ) := by
    exact_mod_cast hcard
  have hPc : (P.card : ℝ) = (B.card : ℝ) * (C \ B).card := by
    simp only [P, card_product]; push_cast; ring
  have hm := card_pairs_meet B (C \ B) S
  have hBc : (B.card : ℝ) ≤ C.card := by exact_mod_cast card_le_card hB
  have hBc' : ((C \ B).card : ℝ) ≤ C.card := by exact_mod_cast card_le_card sdiff_subset
  have hS0 : (0:ℝ) ≤ S.card := Nat.cast_nonneg _
  have e1 : (S.card : ℝ) * (C \ B).card ≤ s0 * C.card :=
    mul_le_mul hSs hBc' (Nat.cast_nonneg _) (le_trans hS0 hSs)
  have e2 : (B.card : ℝ) * S.card ≤ C.card * s0 :=
    mul_le_mul hBc hSs hS0 (Nat.cast_nonneg _)
  have hlow := card_mul_compl_ge hB h1 h2
  linarith

end NashWilliams.Frac
