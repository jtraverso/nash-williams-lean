/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.GlobalCore
import RequestProject.NW18.Sampling.Glue

/-!
# The end of the proof of Theorem 10.9

`finish`: if some pair `(u₂, v₂) ∈ E₂` has both endpoints in about `n/2` pairs of `E₂ ∩ H`, then
`G` is `σ`-extremal.  Indeed the two neighbourhoods are disjoint (triangle-covering), all their
vertices have small degree, and the neighbourhood of `u₂` spans few edges by Proposition 10.8,
so that it is one side of a large cut.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

/-- Number of neighbours of `x` inside `X`, versus the degree. -/
lemma degree_split (x : V) (X : Finset V) :
    (G.degree x : ℝ) = ((univ.filter fun y => G.Adj x y ∧ y ∈ X).card : ℝ) +
      ((univ.filter fun y => G.Adj x y ∧ y ∉ X).card : ℝ) := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]
  have h := card_filter_add_card_filter_not (s := univ.filter (G.Adj x)) (fun y => y ∈ X)
  rw [filter_filter, filter_filter] at h
  exact_mod_cast h.symm

/-- The crossing pairs of a cut, counted from one side. -/
lemma cutSize_ge_sum (X : Finset V) :
    (∑ x ∈ X, ((univ.filter fun y => G.Adj x y ∧ y ∉ X).card : ℝ)) ≤
      (NashWilliams18.cutSize G X : ℝ) := by
  refine le_trans (le_of_eq ?_) (NashWilliams18.Sampling.pairs_le_cutSize G X)
  have : ∀ x, (∑ y, if G.Adj x y ∧ x ∈ X ∧ y ∉ X then (1 : ℝ) else 0) =
      if x ∈ X then ((univ.filter fun y => G.Adj x y ∧ y ∉ X).card : ℝ) else 0 := by
    intro x
    split_ifs with hx
    · rw [card_filter]; push_cast; simp [hx]
    · simp [hx]
  rw [sum_congr rfl fun x _ => this x, sum_ite_mem, univ_inter]

/-- **End of the proof of Theorem 10.9.** -/
theorem finish {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {σ ι L : ℝ}
    (hn1 : 1 ≤ ι * Fintype.card V) (hdeg : 2 * t + ε ≤ σ) (hi : 1 - σ ≤ 2 * L - ι)
    (hM : 0 ≤ 3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι)
    (hcut : (1 - σ) / 4 ≤ (L - ι) * (3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι))
    {u₂ v₂ : V} (h : (u₂, v₂) ∈ E2 G φ t)
    (hX : L * Fintype.card V - 1 / 2 ≤ ((nbr2 G φ t F₀ (3 / 4) u₂).card : ℝ))
    (hY : L * Fintype.card V - 1 / 2 ≤ ((nbr2 G φ t F₀ (3 / 4) v₂).card : ℝ)) :
    NashWilliams18.IsExtremal σ G := by
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set X := nbr2 G φ t F₀ (3 / 4) u₂
  set Y := nbr2 G φ t F₀ (3 / 4) v₂
  have hF := H.F₀pos
  obtain ⟨huv, hneg⟩ := (mem_negPairs G φ).1 (E2_subset G φ t h)
  simp (config := { failIfUnchanged := false }) only at huv hneg
  have memX : ∀ x ∈ X, (u₂, x) ∈ E2 G φ t ∧ 3 / 4 * F₀ ≤ negW φ (u₂, x) := by
    intro x hx; simp only [X, nbr2, mem_filter, mem_univ, true_and] at hx; exact hx
  have memY : ∀ x ∈ Y, (v₂, x) ∈ E2 G φ t ∧ 3 / 4 * F₀ ≤ negW φ (v₂, x) := by
    intro x hx; simp only [Y, nbr2, mem_filter, mem_univ, true_and] at hx; exact hx
  have hdisj : Disjoint X Y := by
    rw [disjoint_left]; intro x hx hy
    obtain ⟨h1, h2⟩ := (mem_negPairs G φ).1 (E2_subset G φ t (memX x hx).1)
    obtain ⟨h3, h4⟩ := (mem_negPairs G φ).1 (E2_subset G φ t (memY x hy).1)
    simp (config := { failIfUnchanged := false }) only at h1 h2 h3 h4
    have := H.hφ.cov u₂ v₂ x huv h1 h3
    linarith
  refine ⟨?_, X, ?_⟩
  · -- many vertices of small degree
    have hsub : X ∪ Y ⊆ univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V) := by
      intro x hx
      rw [mem_filter]
      refine ⟨mem_univ _, ?_⟩
      have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
      rcases mem_union.1 hx with hx | hx
      · have := degree_le_of_E2 G φ H (Or.inr (memX x hx).1)
        nlinarith
      · have := degree_le_of_E2 G φ H (Or.inr (memY x hx).1)
        nlinarith
    have := card_le_card hsub
    rw [card_union_of_disjoint hdisj] at this
    have h' : (X.card : ℝ) + Y.card ≤
        ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + σ) * Fintype.card V)).card : ℝ) := by
      exact_mod_cast this
    have : (1 - σ) * n ≤ (2 * L - ι) * n := mul_le_mul_of_nonneg_right hi (Nat.cast_nonneg _)
    linarith
  · -- the cut `(X, V ∖ X)`
    have hper : ∀ x ∈ X, (3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι) * n ≤
        ((univ.filter fun y => G.Adj x y ∧ y ∉ X).card : ℝ) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := memX x hx
      obtain ⟨A, hA⟩ := H.bip _ hx1 (mem_HH_of_E2 G φ le_rfl hF hx1 hx2)
      simp (config := { failIfUnchanged := false }) only at hA
      have hob := card_obtuse_le G φ H.hφ H.hr.le H.hαr hA u₂ (fun y hy => ((mem_cn G).1 hy).1)
      have hsub : (univ.filter fun y => G.Adj x y ∧ y ∈ X) ⊆
          (cn G u₂ x).filter fun y => φ s(u₂, y) < 0 := by
        intro y hy
        simp only [mem_filter, mem_univ, true_and] at hy
        obtain ⟨h1, h2⟩ := (mem_negPairs G φ).1 (E2_subset G φ t (memX y hy.2).1)
        simp (config := { failIfUnchanged := false }) only at h1 h2
        rw [mem_filter, mem_cn G]
        exact ⟨⟨h1, hy.1⟩, h2⟩
      have hs := card_le_card hsub
      have hs' : ((univ.filter fun y => G.Adj x y ∧ y ∈ X).card : ℝ) ≤
          (((cn G u₂ x).filter fun y => φ s(u₂, y) < 0).card : ℝ) := by exact_mod_cast hs
      have hc := H.cn_le _ hx1
      simp (config := { failIfUnchanged := false }) only at hc
      have hsplit := degree_split G x X
      have hdeg : (G.minDegree : ℝ) ≤ G.degree x := by exact_mod_cast G.minDegree_le_degree x
      have hδ := H.δ
      have hr := H.hr
      have : (1 / 2 + r) * ((cn G u₂ x).card : ℝ) ≤ (1 / 2 + r) * ((1 / 2 + 2 * t) * n) :=
        mul_le_mul_of_nonneg_left hc (by linarith)
      nlinarith
    have hsum : ∑ x ∈ X, (3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι) * n ≤
        ∑ x ∈ X, ((univ.filter fun y => G.Adj x y ∧ y ∉ X).card : ℝ) := sum_le_sum hper
    rw [sum_const, nsmul_eq_mul] at hsum
    have hcs := cutSize_ge_sum G X
    set M := 3 / 4 - ε - (1 / 2 + r) * (1 / 2 + 2 * t) - ι
    have hn0 : 0 ≤ n := Nat.cast_nonneg _
    have hXc : (L - ι) * n ≤ X.card := by nlinarith
    have : (L - ι) * n * (M * n) ≤ X.card * (M * n) :=
      mul_le_mul_of_nonneg_right hXc (mul_nonneg hM hn0)
    have : (1 - σ) / 4 * n ^ 2 ≤ (L - ι) * M * n ^ 2 :=
      mul_le_mul_of_nonneg_right hcut (sq_nonneg _)
    have e : (1 - σ) * n ^ 2 / 4 = (1 - σ) / 4 * n ^ 2 := by ring
    rw [e]
    nlinarith

end NashWilliams.Frac
