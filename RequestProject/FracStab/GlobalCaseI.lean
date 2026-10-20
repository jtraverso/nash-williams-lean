/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.GlobalCaseII

@[expose] public section

/-!
# Theorem 10.9, Case I (Claim 10.9.4)

Both sides `A₀`, `B₀` of the balanced bipartition of the heaviest pair `f₀ = (u₀, v₀) ∈ E₂`
span few edges.  Then the common neighbourhood `N(u₀) ∩ N(v₀)` is one side of a large cut, and
almost all vertices have small degree: those of `N(u₀) ∩ N(v₀)` because they are normal for `f₀`,
and almost all of the others because they lie in the common neighbourhood of a second pair
`f₀' = (u₀', v₀')` with `u₀' ∈ A₀`, `v₀' ∈ B₀` having few neighbours on their own sides.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

lemma half_minus_bound {c n ε r : ℝ} (hc0 : (1 / 2 - 2 * ε) * n ≤ c) (hn : 0 ≤ n) (hr0 : 0 ≤ r)
    (hr : r ≤ 1 / 2) (hε : 0 ≤ ε) : (1 / 4 - ε - r) * n ≤ c / 2 - r * c := by
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ c - (1 / 2 - 2 * ε) * n) (by linarith : (0:ℝ) ≤ 1 / 2 - r),
    mul_nonneg (mul_nonneg hε hr0) hn]

open Classical in
/-- A normal vertex outside `S` of a heavy pair of `E₂` lies in a pair of `E₂`. -/
lemma exists_E2_of_normal {ε t α r κ s ζ F₀ lam : ℝ} (H : Setting G φ ε t α r κ s ζ F₀)
    {ι : ℝ} (hn1 : 1 ≤ ι * Fintype.card V) (hlam : 3 / 4 * F₀ ≤ (1 - α) * (lam * F₀))
    (C : ι / 2 ≤ 1 / 4 - ε - r - s)
    {u v : V} (hw : lam * F₀ ≤ negW φ (u, v)) {A : Finset V} (hA : IsBalBip G φ α u v A)
    {x : V} (hxN : IsNormalV G φ α r u v A x) (hxS : x ∉ SS G φ t F₀ s) :
    ∃ b, (x, b) ∈ E2 G φ t := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := card_pos_of_iota hn1
  have hgood := card_good_partners G φ hA hxN hxS
  have hc0 : (1 / 2 - 2 * ε) * n ≤ (cn G u v).card := (cn_bounds_of_minDegree G H.δ u v).1
  have hb := half_minus_bound hc0 hnpos.le H.hr.le (by linarith [H.hε0, H.hs, H.ht0, card_pos_of_iota hn1, (show 0 ≤ ι by
    by_contra h; push_neg at h; nlinarith)]) H.hε0
  have hpos : (0 : ℝ) < ((otherSide G u v A x).filter fun b =>
      NormalPair G φ α u v x b ∧ b ∉ qpAt G φ t F₀ x).card := by
    have : ι / 2 * n = (ι * n) / 2 := by ring
    have : (ι / 2) * n ≤ (1 / 4 - ε - r - s) * n := mul_le_mul_of_nonneg_right C hnpos.le
    linarith
  obtain ⟨b, hb⟩ := card_pos.1 (by exact_mod_cast hpos)
  rw [mem_filter] at hb
  exact ⟨b, (mem_E2_of_normal G φ H hlam hw hb.2.1 hb.2.2).1⟩

/-- The cut of Case I. -/
lemma cut_caseI {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {β : ℝ}
    {u0 v0 : V} (hf0 : (u0, v0) ∈ E2 G φ t) {A0 : Finset V} (hA0 : A0 ⊆ cn G u0 v0)
    (hin1 : ∑ x ∈ A0, ((A0.filter (G.Adj x)).card : ℝ) ≤ β * (Fintype.card V : ℝ) ^ 2)
    (hin2 : ∑ x ∈ cn G u0 v0 \ A0, (((cn G u0 v0 \ A0).filter (G.Adj x)).card : ℝ) ≤
      β * (Fintype.card V : ℝ) ^ 2) :
    (1 / 4 - ε - 2 * β) * (Fintype.card V : ℝ) ^ 2 ≤
      (NashWilliams18.cutSize G (cn G u0 v0) : ℝ) := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set C := cn G u0 v0
  set B0 := C \ A0
  have hcut := cutSize_ge_sum G C
  -- inner degrees
  have hinner : ∀ x ∈ C, ((univ.filter fun y => G.Adj x y ∧ y ∈ C).card : ℝ) ≤
      (A0.filter (G.Adj x)).card + (B0.filter (G.Adj x)).card := by
    intro x _
    have : (univ.filter fun y => G.Adj x y ∧ y ∈ C) ⊆ A0.filter (G.Adj x) ∪ B0.filter (G.Adj x) := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy
      by_cases h : y ∈ A0
      · exact mem_union_left _ (mem_filter.2 ⟨h, hy.1⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_sdiff.2 ⟨hy.2, h⟩, hy.1⟩)
    exact_mod_cast (card_le_card this).trans (card_union_le _ _)
  have hdeg : ∀ x ∈ C, (3 / 4 - ε) * n - (A0.filter (G.Adj x)).card - (B0.filter (G.Adj x)).card ≤
      ((univ.filter fun y => G.Adj x y ∧ y ∉ C).card : ℝ) := by
    intro x hx
    have h1 := degree_split G x C
    have h2 := hinner x hx
    have h3 : (G.minDegree : ℝ) ≤ G.degree x := by exact_mod_cast G.minDegree_le_degree x
    have h4 : (3 / 4 - ε) * n ≤ G.minDegree := H.δ
    linarith
  have hsum := sum_le_sum hdeg
  -- split the sums over `C = A₀ ∪ B₀`
  have hsplit : ∀ g : V → ℝ, ∑ x ∈ C, g x = ∑ x ∈ A0, g x + ∑ x ∈ B0, g x := by
    intro g
    rw [← sum_sdiff hA0 (f := g)]; ring
  rw [sum_sub_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
  have hAB : ∑ x ∈ C, ((B0.filter (G.Adj x)).card : ℝ) ≤ A0.card * B0.card + β * n ^ 2 := by
    rw [hsplit]
    have : ∑ x ∈ A0, ((B0.filter (G.Adj x)).card : ℝ) ≤ A0.card * B0.card := by
      have : ∀ x ∈ A0, ((B0.filter (G.Adj x)).card : ℝ) ≤ B0.card := fun x _ => by
        exact_mod_cast card_filter_le _ _
      have := sum_le_sum this
      rw [sum_const, nsmul_eq_mul] at this; exact this
    linarith
  have hBA : ∑ x ∈ C, ((A0.filter (G.Adj x)).card : ℝ) ≤ A0.card * B0.card + β * n ^ 2 := by
    rw [hsplit]
    have : ∑ x ∈ B0, ((A0.filter (G.Adj x)).card : ℝ) ≤ B0.card * A0.card := by
      have : ∀ x ∈ B0, ((A0.filter (G.Adj x)).card : ℝ) ≤ A0.card := fun x _ => by
        exact_mod_cast card_filter_le _ _
      have := sum_le_sum this
      rw [sum_const, nsmul_eq_mul] at this; exact this
    linarith
  have hcard : (A0.card : ℝ) + B0.card = C.card := by
    have := card_sdiff_add_card_eq_card hA0
    have : (B0.card : ℝ) + A0.card = C.card := by exact_mod_cast this
    linarith
  have hprod : (A0.card : ℝ) * B0.card ≤ (C.card : ℝ) ^ 2 / 4 := by
    nlinarith [sq_nonneg ((A0.card : ℝ) - B0.card)]
  have hc0 : (1 / 2 - 2 * ε) * n ≤ C.card := (cn_bounds_of_minDegree G H.δ u0 v0).1
  have hc1 : (C.card : ℝ) ≤ (1 / 2 + 2 * t) * n := H.cn_le _ hf0
  have ht := H.ht
  have hε0 := H.hε0
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have key : (1 / 4 - ε) * n ^ 2 ≤ C.card * ((3 / 4 - ε) * n) - (C.card : ℝ) ^ 2 / 2 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ C.card - (1 / 2 - 2 * ε) * n)
      (by nlinarith : (0:ℝ) ≤ (3 / 2 - 2 * ε) * n - C.card - (1 / 2 - 2 * ε) * n)]
  nlinarith

open Classical in
omit [DecidableEq V] in
/-- Vertices of `A` with more than `16 β n` neighbours in `A` are few. -/
lemma card_heavy_lt {β : ℝ} (hβ : 0 < β) (hn : (0 : ℝ) < Fintype.card V) (A : Finset V)
    (hin : ∑ x ∈ A, ((A.filter (G.Adj x)).card : ℝ) < β * (Fintype.card V : ℝ) ^ 2) :
    ((A.filter fun x => 16 * β * Fintype.card V < ((A.filter (G.Adj x)).card : ℝ)).card : ℝ) <
      Fintype.card V / 16 := by
  set n : ℝ := (Fintype.card V : ℝ)
  set T := A.filter fun x => 16 * β * n < ((A.filter (G.Adj x)).card : ℝ)
  have h1 : ∑ x ∈ T, 16 * β * n ≤ ∑ x ∈ A, ((A.filter (G.Adj x)).card : ℝ) := by
    calc ∑ x ∈ T, 16 * β * n ≤ ∑ x ∈ T, ((A.filter (G.Adj x)).card : ℝ) :=
          sum_le_sum fun x hx => (mem_filter.1 hx).2.le
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ => Nat.cast_nonneg _
  rw [sum_const, nsmul_eq_mul] at h1
  have : (T.card : ℝ) * (16 * β * n) < n / 16 * (16 * β * n) := by nlinarith
  exact lt_of_mul_lt_mul_right this (by positivity)

open Classical in
/-- **Case I of Theorem 10.9** (Claim 10.9.4). -/
theorem caseI {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {β ι σ : ℝ}
    (hβ : 0 < β) {u0 v0 : V} (hf0 : (u0, v0) ∈ E2 G φ t) (hF0 : F₀ ≤ negW φ (u0, v0))
    {A0 : Finset V} (hA0 : IsBalBip G φ α u0 v0 A0)
    (hin1 : ∑ x ∈ A0, ((A0.filter (G.Adj x)).card : ℝ) < β * (Fintype.card V : ℝ) ^ 2)
    (hin2 : ∑ x ∈ cn G u0 v0 \ A0, (((cn G u0 v0 \ A0).filter (G.Adj x)).card : ℝ) <
      β * (Fintype.card V : ℝ) ^ 2)
    (hn1 : 1 ≤ ι * Fintype.card V)
    (E1 : (1 - σ) / 4 ≤ 1 / 4 - ε - 2 * β) (E2' : 2 * t + ε ≤ σ)
    (E3 : 2 * (α / (2 * r)) + 2 * ζ + 4 * ε + 32 * β ≤ σ)
    (E4 : α / (2 * r) + ζ + 1 / 16 + ε + ι / 2 < 1 / 4)
    (E5 : 1 / 16 + ε + r + s + ι / 2 ≤ 1 / 4) :
    NashWilliams18.IsExtremal σ G := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  have hnpos : 0 < n := card_pos_of_iota hn1
  have hF := H.F₀pos
  have hα := H.hα
  have hα0 := H.hα0
  have hr := H.hr
  have hε0 := H.hε0
  have hs0 := H.hs
  have hS : ((SS G φ t F₀ s).card : ℝ) ≤ ζ * n := H.S_le
  have hζ : 0 ≤ ζ := by
    by_contra h; push_neg at h
    have : ζ * n < 0 := mul_neg_of_neg_of_pos h hnpos
    have : (0 : ℝ) ≤ (SS G φ t F₀ s).card := Nat.cast_nonneg _
    linarith
  have hι : 0 < ι := by
    by_contra h; push_neg at h; nlinarith
  set C := cn G u0 v0
  set B0 := C \ A0
  refine ⟨?_, C, ?_⟩
  swap
  · -- the cut
    have := cut_caseI G φ H hf0 hA0.1 hin1.le hin2.le
    have e : (1 - σ) * n ^ 2 / 4 = (1 - σ) / 4 * n ^ 2 := by ring
    rw [e]
    exact le_trans (mul_le_mul_of_nonneg_right E1 (sq_nonneg _)) this
  -- choose `u₀'`
  set TA := A0.filter fun x => 16 * β * n < ((A0.filter (G.Adj x)).card : ℝ)
  set TB := B0.filter fun x => 16 * β * n < ((B0.filter (G.Adj x)).card : ℝ)
  have hTA : (TA.card : ℝ) < n / 16 := card_heavy_lt G hβ hnpos A0 hin1
  have hTB : (TB.card : ℝ) < n / 16 := card_heavy_lt G hβ hnpos B0 hin2
  have hNN0 : ((nnSet G φ α r u0 v0 A0).card : ℝ) ≤ α / (2 * r) * n := card_NN_le G φ H hA0
  have hc0 : (1 / 2 - 2 * ε) * n ≤ C.card := (cn_bounds_of_minDegree G H.δ u0 v0).1
  have hcle : (C.card : ℝ) ≤ n := card_cn_le G u0 v0
  have hA0card : (1 / 4 - ε - ι / 2) * n ≤ A0.card := by
    have h2 := hA0.2.2.1
    have hs := card_sdiff_of_subset hA0.1
    have h2' : (2 * (C \ A0).card : ℝ) ≤ C.card + 1 := by exact_mod_cast h2
    rw [hs, Nat.cast_sub (card_le_card hA0.1)] at h2'
    have : ι / 2 * n = (ι * n) / 2 := by ring
    linarith
  obtain ⟨u0', hu0'A, hu0'bad⟩ := exists_mem_not_mem_of_card_lt (T := A0)
    (U := nnSet G φ α r u0 v0 A0 ∪ SS G φ t F₀ s ∪ TA) (by
      have := card_union3_le (nnSet G φ α r u0 v0 A0) (SS G φ t F₀ s) TA
      have : (α / (2 * r) + ζ + 1 / 16) * n < (1 / 4 - ε - ι / 2) * n :=
        mul_lt_mul_of_pos_right (by linarith) hnpos
      linarith)
  simp only [mem_union, not_or] at hu0'bad
  obtain ⟨⟨hu0'NN, hu0'S⟩, hu0'T⟩ := hu0'bad
  have hu0'cn : u0' ∈ C := hA0.1 hu0'A
  have hu0'N := isNormalV_of_not_mem_nnSet G φ hu0'cn hu0'NN
  have hu0'deg : ((A0.filter (G.Adj u0')).card : ℝ) ≤ 16 * β * n := by
    by_contra h; push_neg at h; exact hu0'T (mem_filter.2 ⟨hu0'A, h⟩)
  -- choose `v₀'`
  have hgood := card_good_partners G φ hA0 hu0'N hu0'S
  have hb := half_minus_bound hc0 hnpos.le hr.le (by linarith) hε0
  obtain ⟨v0', hv0'T, hv0'bad⟩ := exists_mem_not_mem_of_card_lt
    (T := (otherSide G u0 v0 A0 u0').filter fun b =>
      NormalPair G φ α u0 v0 u0' b ∧ b ∉ qpAt G φ t F₀ u0') (U := TB) (by
      have : ι / 2 * n = (ι * n) / 2 := by ring
      have : (1 / 16 : ℝ) * n ≤ (1 / 4 - ε - r - s - ι / 2) * n :=
        mul_le_mul_of_nonneg_right (by linarith) hnpos.le
      linarith)
  rw [mem_filter] at hv0'T
  have hv0'B : v0' ∈ B0 := by
    have := hv0'T.1; unfold otherSide at this; rwa [if_pos hu0'A] at this
  have hv0'deg : ((B0.filter (G.Adj v0')).card : ℝ) ≤ 16 * β * n := by
    by_contra h; push_neg at h; exact hv0'bad (mem_filter.2 ⟨hv0'B, h⟩)
  have hlam1 : 3 / 4 * F₀ ≤ (1 - α) * (1 * F₀) := by nlinarith
  obtain ⟨hf0', hw0'⟩ := mem_E2_of_normal G φ H hlam1 (by linarith) hv0'T.2.1 hv0'T.2.2
  obtain ⟨A0', hA0'⟩ := H.bip _ hf0' (mem_HH_of_E2 G φ (ρ := 1 - α) (by linarith) hF hf0'
    (by linarith))
  simp (config := { failIfUnchanged := false }) only at hA0'
  set C' := cn G u0' v0'
  have hc0' : (1 / 2 - 2 * ε) * n ≤ C'.card := (cn_bounds_of_minDegree G H.δ u0' v0').1
  have hNN0' : ((nnSet G φ α r u0' v0' A0').card : ℝ) ≤ α / (2 * r) * n := card_NN_le G φ H hA0'
  -- the intersection of the two common neighbourhoods is small
  have hinter : ((C ∩ C').card : ℝ) ≤ 32 * β * n := by
    have : C ∩ C' ⊆ A0.filter (G.Adj u0') ∪ B0.filter (G.Adj v0') := by
      intro x hx
      rw [mem_inter] at hx
      have hx2 := (mem_cn G).1 hx.2
      by_cases h : x ∈ A0
      · exact mem_union_left _ (mem_filter.2 ⟨h, hx2.1⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨mem_sdiff.2 ⟨hx.1, h⟩, hx2.2⟩)
    have := (card_le_card this).trans (card_union_le _ _)
    have : ((C ∩ C').card : ℝ) ≤ (A0.filter (G.Adj u0')).card + (B0.filter (G.Adj v0')).card := by
      exact_mod_cast this
    linarith
  have hunion : (n - ((C ∪ C').card : ℝ)) ≤ (4 * ε + 32 * β) * n := by
    have := card_union_add_card_inter C C'
    have : ((C ∪ C').card : ℝ) + (C ∩ C').card = C.card + C'.card := by exact_mod_cast this
    linarith
  -- low degree vertices
  have hlow : ∀ x, x ∉ nnSet G φ α r u0 v0 A0 ∪ nnSet G φ α r u0' v0' A0' ∪ SS G φ t F₀ s ∪
      (univ \ (C ∪ C')) → (G.degree x : ℝ) ≤ (3 / 4 + σ) * n := by
    intro x hx
    simp only [mem_union, not_or, mem_sdiff, mem_univ, true_and] at hx
    obtain ⟨⟨⟨hx1, hx2⟩, hx3⟩, hx4⟩ := hx
    have hEx : ∃ b, (x, b) ∈ E2 G φ t := by
      by_cases h : x ∈ C
      · exact exists_E2_of_normal G φ H hn1 hlam1 (by linarith) (by linarith : 1 * F₀ ≤ negW φ (u0, v0)) hA0
          (isNormalV_of_not_mem_nnSet G φ h hx1) hx3
      · have h : x ∈ C' := by
          by_contra h'; exact hx4 ⟨h, h'⟩
        have hlam2 : 3 / 4 * F₀ ≤ (1 - α) * ((1 - α) * F₀) := by
          have := mul_le_mul_of_nonneg_right (aux_rho3 hα0 hα) hF.le
          linarith
        exact exists_E2_of_normal G φ H hn1 hlam2 (by linarith) (by linarith : (1 - α) * F₀ ≤ negW φ (u0', v0')) hA0'
          (isNormalV_of_not_mem_nnSet G φ h hx2) hx3
    obtain ⟨b, hb⟩ := hEx
    have hd1 := degree_le_of_E2 G φ H (Or.inl hb)
    have hd2 : (3 / 4 + 2 * t + ε) * n ≤ (3 / 4 + σ) * n :=
      mul_le_mul_of_nonneg_right (by linarith) hnpos.le
    exact hd1.trans hd2
  set Bad := nnSet G φ α r u0 v0 A0 ∪ nnSet G φ α r u0' v0' A0' ∪ SS G φ t F₀ s ∪ (univ \ (C ∪ C'))
  have hsub : univ \ Bad ⊆ univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V) := by
    intro x hx
    rw [mem_sdiff] at hx
    exact mem_filter.2 ⟨mem_univ _, hlow x hx.2⟩
  have h1 := card_le_card hsub
  have h2 : ((univ \ Bad).card : ℝ) = n - Bad.card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Nat.cast_sub (card_le_univ _)]
  have h3 := card_union4_le (nnSet G φ α r u0 v0 A0) (nnSet G φ α r u0' v0' A0') (SS G φ t F₀ s)
    (univ \ (C ∪ C'))
  have h4 : ((univ \ (C ∪ C')).card : ℝ) = n - (C ∪ C').card := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Nat.cast_sub (card_le_univ _)]
  have h1' : ((univ \ Bad).card : ℝ) ≤
      ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)).card : ℝ) := by
    exact_mod_cast h1
  have hE3 : (2 * (α / (2 * r)) + 2 * ζ + 4 * ε + 32 * β) * n ≤ σ * n :=
    mul_le_mul_of_nonneg_right E3 hnpos.le
  have hgoal : (1 - σ) * n ≤ ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)).card : ℝ) := by
    linarith only [h1', h2, h3, h4, hNN0, hNN0', hS, hunion, hE3]
  exact hgoal

end NashWilliams.Frac
