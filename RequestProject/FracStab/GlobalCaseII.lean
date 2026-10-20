/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.GlobalFinish

@[expose] public section

/-!
# Theorem 10.9, Case II (Claims 10.9.5, 10.9.7 and 10.9.8)

One side `A₀` of the balanced bipartition of the heaviest pair `f₀ = (u₀, v₀) ∈ E₂` spans at least
`β n²/2` edges.  We find successively

* `u₁ ∈ A₀` with many neighbours in `A₀` and a partner `v₁` with `f₁ = (u₁, v₁) ∈ E₂`
  (`step_u1v1`);
* a `u₁`-obtuse vertex `u₂` of `f₁` to which the gadget applies (`step_u2`);
* a `v₁`-obtuse vertex `v₂` of `f₂ = (v₁, u₂)` to which the gadget applies (`step_v2`),

so that `(u₂, v₂)` satisfies the hypotheses of `finish`.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

omit [Fintype V] in
lemma exists_mem_not_mem_of_card_lt {T U : Finset V} (h : (U.card : ℝ) < T.card) :
    ∃ x ∈ T, x ∉ U := by
  by_contra hc
  push_neg at hc
  have := card_le_card (show T ⊆ U from hc)
  have : (T.card : ℝ) ≤ U.card := by exact_mod_cast this
  linarith

omit [Fintype V] in
lemma card_union3_le (A B C : Finset V) :
    ((A ∪ B ∪ C).card : ℝ) ≤ A.card + B.card + C.card := by
  have h1 := card_union_le (A ∪ B) C
  have h2 := card_union_le A B
  have : (A ∪ B ∪ C).card ≤ A.card + B.card + C.card := by omega
  exact_mod_cast this

omit [Fintype V] in
lemma card_union4_le (A B C D : Finset V) :
    ((A ∪ B ∪ C ∪ D).card : ℝ) ≤ A.card + B.card + C.card + D.card := by
  have h1 := card_union_le (A ∪ B ∪ C) D
  have h2 := card_union_le (A ∪ B) C
  have h3 := card_union_le A B
  have : (A ∪ B ∪ C ∪ D).card ≤ A.card + B.card + C.card + D.card := by omega
  exact_mod_cast this

omit [DecidableEq V] in
lemma card_pos_of_iota {ι : ℝ} (hn1 : 1 ≤ ι * Fintype.card V) : (0 : ℝ) < Fintype.card V := by
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card V)).eq_or_lt with h | h
  · rw [← h] at hn1; simp at hn1; linarith
  · exact h

open Classical in
/-- Claim 10.9.5, first part: the pair `f₁ = (u₁, v₁)`. -/
lemma step_u1v1 {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {β ι : ℝ}
    {u0 v0 : V} {A0 : Finset V} (hF0 : F₀ ≤ negW φ (u0, v0)) (hA0 : IsBalBip G φ α u0 v0 A0)
    (hin : β * (Fintype.card V : ℝ) ^ 2 ≤ ∑ x ∈ A0, ((A0.filter (G.Adj x)).card : ℝ))
    (hn1 : 1 ≤ ι * Fintype.card V)
    (C1 : α / (2 * r) + ζ < β / 2) (C2 : α / (2 * r) + ζ + ι / 2 < 1 / 4 - ε - r - s) :
    ∃ u1 v1, u1 ∈ A0 ∧ β / 2 * Fintype.card V ≤ ((A0.filter (G.Adj u1)).card : ℝ) ∧
      u1 ∉ SS G φ t F₀ s ∧ v1 ∉ SS G φ t F₀ s ∧ IsNormalV G φ α r u0 v0 A0 v1 ∧
      v1 ∉ A0 ∧ (u1, v1) ∈ E2 G φ t ∧ (1 - α) * F₀ ≤ negW φ (u1, v1) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := card_pos_of_iota hn1
  have hF := H.F₀pos
  have hα := H.hα
  have hα0 := H.hα0
  have hr := H.hr
  have hε0 := H.hε0
  have hS : ((SS G φ t F₀ s).card : ℝ) ≤ ζ * n := H.S_le
  have hζ : 0 ≤ ζ := by
    by_contra h; push_neg at h
    have : ζ * n < 0 := mul_neg_of_neg_of_pos h hnpos
    have : (0 : ℝ) ≤ (SS G φ t F₀ s).card := Nat.cast_nonneg _
    linarith
  have hν : 0 ≤ α / (2 * r) := by positivity
  have hβ : 0 ≤ β := by linarith
  -- the set `U` of vertices with many neighbours in `A₀`
  set U := A0.filter fun w => β / 2 * n ≤ ((A0.filter (G.Adj w)).card : ℝ)
  have hU : β / 2 * n ≤ U.card := by
    have hsplit := sum_filter_add_sum_filter_not A0
      (fun w => β / 2 * n ≤ ((A0.filter (G.Adj w)).card : ℝ))
      (fun x => ((A0.filter (G.Adj x)).card : ℝ))
    have h1 : ∑ x ∈ U, ((A0.filter (G.Adj x)).card : ℝ) ≤ U.card * n := by
      have : ∀ x ∈ U, ((A0.filter (G.Adj x)).card : ℝ) ≤ n := fun x _ => by
        rw [hn]; exact_mod_cast card_le_univ _
      have := sum_le_sum this
      rw [sum_const, nsmul_eq_mul] at this; exact this
    have h2 : ∑ x ∈ A0.filter (fun w => ¬ (β / 2 * n ≤ ((A0.filter (G.Adj w)).card : ℝ))),
        ((A0.filter (G.Adj x)).card : ℝ) ≤ n * (β / 2 * n) := by
      have : ∀ x ∈ A0.filter (fun w => ¬ (β / 2 * n ≤ ((A0.filter (G.Adj w)).card : ℝ))),
          ((A0.filter (G.Adj x)).card : ℝ) ≤ β / 2 * n := fun x hx => by
        rw [mem_filter] at hx; push_neg at hx; exact hx.2.le
      have h3 := sum_le_sum this
      rw [sum_const, nsmul_eq_mul] at h3
      have h4 : ((A0.filter (fun w => ¬ (β / 2 * n ≤ ((A0.filter (G.Adj w)).card : ℝ)))).card : ℝ)
          ≤ n := by rw [hn]; exact_mod_cast card_le_univ _
      have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ β / 2 * n)
      linarith
    have : β * n ^ 2 ≤ U.card * n + n * (β / 2 * n) := by linarith
    have : β / 2 * n * n ≤ U.card * n := by nlinarith
    exact le_of_mul_le_mul_right this hnpos
  -- choose `u₁`
  set NN0 := nnSet G φ α r u0 v0 A0
  have hNN0 : (NN0.card : ℝ) ≤ α / (2 * r) * n := card_NN_le G φ H hA0
  obtain ⟨u1, hu1U, hu1bad⟩ := exists_mem_not_mem_of_card_lt (T := U) (U := NN0 ∪ SS G φ t F₀ s) (by
    have := card_union_le NN0 (SS G φ t F₀ s)
    have : ((NN0 ∪ SS G φ t F₀ s).card : ℝ) ≤ NN0.card + (SS G φ t F₀ s).card := by
      exact_mod_cast this
    have : (α / (2 * r) + ζ) * n < β / 2 * n := mul_lt_mul_of_pos_right C1 hnpos
    linarith)
  rw [mem_union, not_or] at hu1bad
  obtain ⟨hu1A, hu1d⟩ := mem_filter.1 hu1U
  have hu1cn : u1 ∈ cn G u0 v0 := hA0.1 hu1A
  have hu1N := isNormalV_of_not_mem_nnSet G φ hu1cn hu1bad.1
  -- choose `v₁`
  have hgood := card_good_partners G φ hA0 hu1N hu1bad.2
  have hc0 : (1 / 2 - 2 * ε) * n ≤ (cn G u0 v0).card := (cn_bounds_of_minDegree G H.δ u0 v0).1
  have hcle : ((cn G u0 v0).card : ℝ) ≤ n := card_cn_le G u0 v0
  have hrc : r * ((cn G u0 v0).card : ℝ) ≤ r * n := mul_le_mul_of_nonneg_left hcle hr.le
  obtain ⟨v1, hv1T, hv1bad⟩ := exists_mem_not_mem_of_card_lt
    (T := (otherSide G u0 v0 A0 u1).filter fun b =>
      NormalPair G φ α u0 v0 u1 b ∧ b ∉ qpAt G φ t F₀ u1) (U := NN0 ∪ SS G φ t F₀ s) (by
    have := card_union_le NN0 (SS G φ t F₀ s)
    have : ((NN0 ∪ SS G φ t F₀ s).card : ℝ) ≤ NN0.card + (SS G φ t F₀ s).card := by
      exact_mod_cast this
    have : (α / (2 * r) + ζ + ι / 2) * n < (1 / 4 - ε - r - s) * n :=
      mul_lt_mul_of_pos_right C2 hnpos
    nlinarith)
  rw [mem_union, not_or] at hv1bad
  rw [mem_filter] at hv1T
  have hv1o : v1 ∈ cn G u0 v0 \ A0 := by
    have := hv1T.1; unfold otherSide at this; rwa [if_pos hu1A] at this
  have hv1cn := (mem_sdiff.1 hv1o).1
  have hv1N := isNormalV_of_not_mem_nnSet G φ hv1cn hv1bad.1
  have hlam : 3 / 4 * F₀ ≤ (1 - α) * (1 * F₀) := by nlinarith
  obtain ⟨hE, hw⟩ := mem_E2_of_normal G φ H hlam (by linarith) hv1T.2.1 hv1T.2.2
  exact ⟨u1, v1, hu1A, hu1d, hu1bad.2, hv1bad.2, hv1N, (mem_sdiff.1 hv1o).2, hE, by linarith⟩

lemma aux_rho1 {α : ℝ} (h0 : 0 ≤ α) (h : α ≤ 1 / 100) : 9 / 10 ≤ (1 - α) * (1 - α) := by
  nlinarith

lemma aux_rho2 {α κ : ℝ} (h0 : 0 ≤ α) (h : α ≤ 1 / 100) (k0 : 0 ≤ κ) (k : κ ≤ 1 / 100) :
    9 / 10 ≤ (1 - κ) * ((1 - α) + (1 - α)) - 1 := by
  nlinarith

lemma aux_rho3 {α : ℝ} (h0 : 0 ≤ α) (h : α ≤ 1 / 100) : 3 / 4 ≤ (1 - α) * (1 - α) := by
  nlinarith

lemma aux_rho4 {α κ : ℝ} (h0 : 0 ≤ α) (h : α ≤ 1 / 100) (k0 : 0 ≤ κ) (k : κ ≤ 1 / 100) :
    3 / 4 ≤ (1 - κ) * ((1 - α) + 9 / 10) - 1 := by
  nlinarith

open Classical in
/-- Claims 10.9.5 (second part) and 10.9.7: the vertex `u₂`. -/
lemma step_u2 {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {β ι : ℝ}
    {u0 v0 : V} {A0 : Finset V} (hF0 : F₀ ≤ negW φ (u0, v0)) (hn1 : 1 ≤ ι * Fintype.card V)
    {u1 v1 : V} (hu1d : β / 2 * Fintype.card V ≤ ((A0.filter (G.Adj u1)).card : ℝ))
    (hu1S : u1 ∉ SS G φ t F₀ s) (hv1N : IsNormalV G φ α r u0 v0 A0 v1) (hv1A : v1 ∉ A0)
    (hv1S : v1 ∉ SS G φ t F₀ s) (hf1 : (u1, v1) ∈ E2 G φ t) (hw1 : (1 - α) * F₀ ≤ negW φ (u1, v1))
    (C3 : α / (2 * r) + κ + ζ + s < β / 2 - r) :
    ∃ u2, u2 ∉ SS G φ t F₀ s ∧ (v1, u2) ∈ E2 G φ t ∧ (1 - α) * F₀ ≤ negW φ (v1, u2) ∧
      (1 / 2 - ε - t - r - 3 * s - κ) * Fintype.card V - 1 / 2 ≤
        ((nbr2 G φ t F₀ (9 / 10) u2).card : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := card_pos_of_iota hn1
  have hF := H.F₀pos
  have hα := H.hα
  have hα0 := H.hα0
  have hκ := H.hκ
  have hκ0 := H.hκ0
  have hr := H.hr
  -- the bipartition of `f₁`
  obtain ⟨A1, hA1⟩ := H.bip _ hf1 (mem_HH_of_E2 G φ (ρ := 1 - α) (by linarith) hF hf1 hw1)
  simp (config := { failIfUnchanged := false }) only at hA1
  -- normal partners of `v₁` in `A₀`
  have hoth : otherSide G u0 v0 A0 v1 = A0 := by unfold otherSide; rw [if_neg hv1A]
  have hbadv1 : ((A0.filter fun b => ¬ NormalPair G φ α u0 v0 v1 b).card : ℝ) ≤ r * n := by
    have h := hv1N; unfold IsNormalV at h; rw [hoth] at h
    have hcle : ((cn G u0 v0).card : ℝ) ≤ n := card_cn_le G u0 v0
    have := mul_le_mul_of_nonneg_left hcle hr.le
    linarith
  set T := (A0.filter (G.Adj u1)).filter fun b => NormalPair G φ α u0 v0 v1 b
  have hT : (β / 2 - r) * n ≤ T.card := by
    have hsub : A0.filter (G.Adj u1) ⊆ T ∪ A0.filter fun b => ¬ NormalPair G φ α u0 v0 v1 b := by
      intro x hx
      by_cases h : NormalPair G φ α u0 v0 v1 x
      · exact mem_union_left _ (mem_filter.2 ⟨hx, h⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨(mem_filter.1 hx).1, h⟩)
    have := (card_le_card hsub).trans (card_union_le _ _)
    have : ((A0.filter (G.Adj u1)).card : ℝ) ≤ T.card +
        ((A0.filter fun b => ¬ NormalPair G φ α u0 v0 v1 b).card : ℝ) := by exact_mod_cast this
    linarith
  -- the bad vertices
  set NN1 := nnSet G φ α r u1 v1 A1
  have hNN1 : (NN1.card : ℝ) ≤ α / (2 * r) * n := card_NN_le G φ H hA1
  have hUC1 := H.clean _ hf1
  simp (config := { failIfUnchanged := false }) only at hUC1
  have hS : ((SS G φ t F₀ s).card : ℝ) ≤ ζ * n := H.S_le
  have hQ : ((qpAt G φ t F₀ v1).card : ℝ) < s * n := card_qpAt_lt G φ hv1S
  obtain ⟨u2, hu2T, hu2bad⟩ := exists_mem_not_mem_of_card_lt (T := T)
    (U := NN1 ∪ (ucSet G φ κ u1 v1) ∪ SS G φ t F₀ s ∪ qpAt G φ t F₀ v1) (by
      have := card_union4_le NN1 (ucSet G φ κ u1 v1) (SS G φ t F₀ s) (qpAt G φ t F₀ v1)
      have : (α / (2 * r) + κ + ζ + s) * n < (β / 2 - r) * n := mul_lt_mul_of_pos_right C3 hnpos
      linarith)
  simp only [mem_union, not_or] at hu2bad
  obtain ⟨⟨⟨hu2NN, hu2UC⟩, hu2S⟩, hu2Q⟩ := hu2bad
  simp only [T, mem_filter] at hu2T
  obtain ⟨⟨-, hu1u2⟩, hNP⟩ := hu2T
  have hNP' := hNP
  obtain ⟨hv1u2, hneg2, hw2⟩ := hNP'
  obtain ⟨huv1, hneg1⟩ := (mem_negPairs G φ).1 (E2_subset G φ t hf1)
  simp (config := { failIfUnchanged := false }) only at huv1 hneg1
  have hu2cn : u2 ∈ cn G u1 v1 := (mem_cn G).2 ⟨hu1u2, hv1u2⟩
  have hu2N := isNormalV_of_not_mem_nnSet G φ hu2cn hu2NN
  have hu2c : ¬ IsUnclean G φ κ u1 v1 u2 := fun h => hu2UC ((mem_ucSet G φ).2 ⟨hu2cn, Or.inl h⟩)
  have hpos : 0 < φ s(u1, u2) := by
    have := H.hφ.cov u1 v1 u2 huv1 hu1u2 hv1u2
    linarith
  have hF0' : (1 - α) * F₀ ≤ -φ s(v1, u2) := by
    unfold negW at hF0; simp (config := { failIfUnchanged := false }) only at hF0
    have := mul_le_mul_of_nonneg_left hF0 (by linarith : (0:ℝ) ≤ 1 - α)
    linarith
  have hαF : α * F₀ ≤ 1 / 100 * F₀ := mul_le_mul_of_nonneg_right hα hF.le
  have hg := gadget G φ H (lam := 1 - α) (μ := 1 - α) (ρ := 9 / 10) (aux_rho1 hα0 hα)
    (aux_rho2 hα0 hα hκ0 hκ) (by norm_num) hf1 hw1 hA1 hu2cn hu2S hu1S hu2N hu2c hpos hF0'
  have hlam : 3 / 4 * F₀ ≤ (1 - α) * (1 * F₀) := by linarith
  obtain ⟨hE2, hwE2⟩ := mem_E2_of_normal G φ H hlam (by linarith) hNP hu2Q
  exact ⟨u2, hu2S, hE2, by linarith, hg⟩

open Classical in
/-- Claim 10.9.8: the vertex `v₂`. -/
lemma step_v2 {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {ι : ℝ}
    (hn1 : 1 ≤ ι * Fintype.card V) {v1 u2 : V} (hv1S : v1 ∉ SS G φ t F₀ s) (hf2 : (v1, u2) ∈ E2 G φ t)
    (hw2 : (1 - α) * F₀ ≤ negW φ (v1, u2))
    (hX : (1 / 2 - ε - t - r - 3 * s - κ) * Fintype.card V - 1 / 2 ≤
        ((nbr2 G φ t F₀ (9 / 10) u2).card : ℝ))
    (C4 : α / (2 * r) + κ + ζ + 1 / 4 + ε + ι / 2 < 1 / 2 - ε - t - r - 3 * s - κ) :
    ∃ v2, (u2, v2) ∈ E2 G φ t ∧ (1 / 2 - ε - t - r - 3 * s - κ) * Fintype.card V - 1 / 2 ≤
        ((nbr2 G φ t F₀ (3 / 4) v2).card : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := card_pos_of_iota hn1
  have hF := H.F₀pos
  have hα := H.hα
  have hα0 := H.hα0
  have hκ := H.hκ
  have hκ0 := H.hκ0
  obtain ⟨A2, hA2⟩ := H.bip _ hf2 (mem_HH_of_E2 G φ (ρ := 1 - α) (by linarith) hF hf2 hw2)
  simp (config := { failIfUnchanged := false }) only at hA2
  obtain ⟨hvu, hneg⟩ := (mem_negPairs G φ).1 (E2_subset G φ t hf2)
  simp (config := { failIfUnchanged := false }) only at hvu hneg
  set X := nbr2 G φ t F₀ (9 / 10) u2
  set T := X ∩ G.neighborFinset v1
  have hT : ((1 / 2 - ε - t - r - 3 * s - κ) - (1 / 4 + ε)) * n - 1 / 2 ≤ T.card := by
    have h1 := card_inter_add_card_union X (G.neighborFinset v1)
    have h2 : (X ∪ G.neighborFinset v1).card ≤ Fintype.card V := card_le_univ _
    have h3 : (G.neighborFinset v1).card = G.degree v1 := G.card_neighborFinset_eq_degree v1
    have hdeg : (G.minDegree : ℝ) ≤ G.degree v1 := by exact_mod_cast G.minDegree_le_degree v1
    have hδ : (3 / 4 - ε) * n ≤ G.minDegree := H.δ
    have : (T.card : ℝ) + (X ∪ G.neighborFinset v1).card = X.card + G.degree v1 := by
      rw [← h3]; exact_mod_cast h1
    have : ((X ∪ G.neighborFinset v1).card : ℝ) ≤ n := by rw [hn]; exact_mod_cast h2
    linarith
  set NN2 := nnSet G φ α r v1 u2 A2
  have hNN2 : (NN2.card : ℝ) ≤ α / (2 * r) * n := card_NN_le G φ H hA2
  have hUC2 := H.clean _ hf2
  simp (config := { failIfUnchanged := false }) only at hUC2
  have hS : ((SS G φ t F₀ s).card : ℝ) ≤ ζ * n := H.S_le
  obtain ⟨v2, hv2T, hv2bad⟩ := exists_mem_not_mem_of_card_lt (T := T)
    (U := NN2 ∪ (ucSet G φ κ v1 u2) ∪ SS G φ t F₀ s) (by
      have := card_union3_le NN2 (ucSet G φ κ v1 u2) (SS G φ t F₀ s)
      have : (α / (2 * r) + κ + ζ) * n <
          ((1 / 2 - ε - t - r - 3 * s - κ) - (1 / 4 + ε) - ι / 2) * n :=
        mul_lt_mul_of_pos_right (by linarith) hnpos
      have : ι / 2 * n = (ι * n) / 2 := by ring
      linarith)
  simp only [mem_union, not_or] at hv2bad
  obtain ⟨⟨hv2NN, hv2UC⟩, hv2S⟩ := hv2bad
  rw [mem_inter, SimpleGraph.mem_neighborFinset] at hv2T
  obtain ⟨hv2X, hv1v2⟩ := hv2T
  simp only [X, nbr2, mem_filter, mem_univ, true_and] at hv2X
  obtain ⟨hE, hw⟩ := hv2X
  obtain ⟨hu2v2, hneg2⟩ := (mem_negPairs G φ).1 (E2_subset G φ t hE)
  simp (config := { failIfUnchanged := false }) only at hu2v2 hneg2
  have hv2cn : v2 ∈ cn G v1 u2 := (mem_cn G).2 ⟨hv1v2, hu2v2⟩
  have hv2N := isNormalV_of_not_mem_nnSet G φ hv2cn hv2NN
  have hv2c : ¬ IsUnclean G φ κ v1 u2 v2 := fun h => hv2UC ((mem_ucSet G φ).2 ⟨hv2cn, Or.inl h⟩)
  have hpos : 0 < φ s(v1, v2) := by
    have := H.hφ.cov v1 u2 v2 hvu hv1v2 hu2v2
    linarith
  have hw' : 9 / 10 * F₀ ≤ -φ s(u2, v2) := hw
  have hg := gadget G φ H (lam := 1 - α) (μ := 9 / 10) (ρ := 3 / 4) (aux_rho3 hα0 hα)
    (aux_rho4 hα0 hα hκ0 hκ) le_rfl hf2 hw2 hA2 hv2cn hv2S hv1S hv2N hv2c hpos hw'
  exact ⟨v2, hE, hg⟩

/-- **Case II of Theorem 10.9**: if one side `A₀` of the balanced bipartition of the heaviest
pair spans many edges, then `G` is `σ`-extremal. -/
theorem caseII {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {β ι σ : ℝ}
    {u0 v0 : V} {A0 : Finset V} (hF0 : F₀ ≤ negW φ (u0, v0)) (hA0 : IsBalBip G φ α u0 v0 A0)
    (hin : β * (Fintype.card V : ℝ) ^ 2 ≤ ∑ x ∈ A0, ((A0.filter (G.Adj x)).card : ℝ))
    (hn1 : 1 ≤ ι * Fintype.card V)
    (C1 : α / (2 * r) + ζ < β / 2) (C2 : α / (2 * r) + ζ + ι / 2 < 1 / 4 - ε - r - s)
    (C3 : α / (2 * r) + κ + ζ + s < β / 2 - r)
    (C4 : α / (2 * r) + κ + ζ + 1 / 4 + ε + ι / 2 < 1 / 2 - ε - t - r - 3 * s - κ)
    (hdeg : 2 * t + ε ≤ σ) (hi : 1 - σ ≤ 2 * (1 / 2 - ε - t - r - 3 * s - κ) - ι)
    (hM : 0 ≤ 3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι)
    (hcut : (1 - σ) / 4 ≤ ((1 / 2 - ε - t - r - 3 * s - κ) - ι) *
      (3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι)) :
    NashWilliams18.IsExtremal σ G := by
  obtain ⟨u1, v1, -, hu1d, hu1S, hv1S, hv1N, hv1A, hf1, hw1⟩ :=
    step_u1v1 G φ H hF0 hA0 hin hn1 C1 C2
  obtain ⟨u2, -, hf2, hw2, hX⟩ :=
    step_u2 G φ H hF0 hn1 hu1d hu1S hv1N hv1A hv1S hf1 hw1 C3
  obtain ⟨v2, hE, hY⟩ := step_v2 G φ H hn1 hv1S hf2 hw2 hX C4
  have hmono : nbr2 G φ t F₀ (9 / 10) u2 ⊆ nbr2 G φ t F₀ (3 / 4) u2 := by
    intro x hx
    simp only [nbr2, mem_filter, mem_univ, true_and] at hx ⊢
    exact ⟨hx.1, le_trans (by nlinarith [H.F₀pos]) hx.2⟩
  have hX' : (1 / 2 - ε - t - r - 3 * s - κ) * Fintype.card V - 1 / 2 ≤
      ((nbr2 G φ t F₀ (3 / 4) u2).card : ℝ) :=
    le_trans hX (by exact_mod_cast card_le_card hmono)
  exact finish G φ H hn1 hdeg hi hM hcut hE hX' hY

end NashWilliams.Frac
