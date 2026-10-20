/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Setup

/-!
# The bipartition `P*` (Claims 12.6.4 and 12.6.5)

`sideP G p A` is the bipartition `P* = (V₁ ∪ V₂, V₃ ∪ V₄)` of the paper built from the new
partition `newPart G p A`.  We check the hypotheses of Lemma 15.9 for `G` with this
bipartition and `γ = 100 s`:

* `twoExtremal_126` — `G[P*]` is `γ`-extremal (Claim 12.6.5);
* `crossBalanced_126` — `G[P*]` is `γ`-cross-balanced (Claim 12.6.4);
* `highInt_mem_126` — every vertex with `IntDeg ≥ 0.371 n` lies in `A`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The bipartition `P*`. -/
def sideP (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (A : Finset V) (x : V) :
    Fin 2 :=
  side4 (newPart G p A x)

/-- Degree of `v` into the side `σ` of the old partition. -/
def sideDeg (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (v : V) (σ : Fin 2) : ℕ :=
  (univ.filter (fun w => G.Adj v w ∧ side4 (p w) = σ)).card

section

variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V} {s : ℝ}

lemma sideP_of_not_mem {x : V} (hx : x ∉ A) : sideP G p A x = side4 (p x) := by
  simp [sideP, newPart_of_not_mem hx]

lemma sideDeg_zero (v : V) : sideDeg G p v 0 = degT G p v 0 + degT G p v 1 := by
  unfold sideDeg degT
  rw [← card_union_of_disjoint]
  · congr 1; ext w
    simp only [mem_filter, mem_univ, true_and, mem_union]
    have : side4 (p w) = 0 ↔ p w = 0 ∨ p w = 1 := by
      generalize p w = i; revert i; decide
    rw [this]; tauto
  · rw [disjoint_filter]; intro w _ h1 h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)

lemma sideDeg_one (v : V) : sideDeg G p v 1 = degT G p v 2 + degT G p v 3 := by
  unfold sideDeg degT
  rw [← card_union_of_disjoint]
  · congr 1; ext w
    simp only [mem_filter, mem_univ, true_and, mem_union]
    have : side4 (p w) = 1 ↔ p w = 2 ∨ p w = 3 := by
      generalize p w = i; revert i; decide
    rw [this]; tauto
  · rw [disjoint_filter]; intro w _ h1 h2; rw [h1.2] at h2; exact absurd h2.2 (by decide)

lemma partDeg_sideP_le (v : V) (σ : Fin 2) :
    partDeg G (sideP G p A) v σ ≤ sideDeg G p v σ + A.card := by
  unfold partDeg sideDeg
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro w hw
  simp only [mem_filter, mem_univ, true_and, mem_union] at hw ⊢
  by_cases hwA : w ∈ A
  · exact Or.inr hwA
  · exact Or.inl ⟨hw.1, by rw [← sideP_of_not_mem (G := G) (p := p) hwA]; exact hw.2⟩

lemma sideDeg_le_partDeg (v : V) (σ : Fin 2) :
    sideDeg G p v σ ≤ partDeg G (sideP G p A) v σ + A.card := by
  unfold partDeg sideDeg
  refine (card_le_card ?_).trans (card_union_le _ _)
  intro w hw
  simp only [mem_filter, mem_univ, true_and, mem_union] at hw ⊢
  by_cases hwA : w ∈ A
  · exact Or.inr hwA
  · exact Or.inl ⟨hw.1, by rw [sideP_of_not_mem (G := G) (p := p) hwA]; exact hw.2⟩

omit [Fintype V] [DecidableEq V] in
lemma p_cases (x : V) : p x = 0 ∨ p x = 1 ∨ p x = 2 ∨ p x = 3 := by
  rcases p x with ⟨k, hk⟩; interval_cases k <;> simp

/-- Degree into the own side of a vertex: its class and at most its abnormal pairs. -/
lemma sideDeg_own_le (v : V) :
    sideDeg G p v (side4 (p v)) ≤ (clsT p (p v)).card + (abnSet G p v).card := by
  rcases p_cases (p := p) v with hc | hc | hc | hc
  · have h1 := degT_le_abn_forbidden G p v 1 (by rw [hc]; decide)
    have h0 := degT_le_class G p v 0
    rw [hc, show side4 0 = 0 by decide, sideDeg_zero]; omega
  · have h1 := degT_le_abn_forbidden G p v 0 (by rw [hc]; decide)
    have h0 := degT_le_class G p v 1
    rw [hc, show side4 1 = 0 by decide, sideDeg_zero]; omega
  · have h1 := degT_le_abn_forbidden G p v 3 (by rw [hc]; decide)
    have h0 := degT_le_class G p v 2
    rw [hc, show side4 2 = 1 by decide, sideDeg_one]; omega
  · have h1 := degT_le_abn_forbidden G p v 2 (by rw [hc]; decide)
    have h0 := degT_le_class G p v 3
    rw [hc, show side4 3 = 1 by decide, sideDeg_one]; omega

/-- Degree into the other side of a vertex: both classes there, up to abnormal pairs. -/
lemma sideDeg_other_ge (h : Setup126 G p A s) (v : V) (σ : Fin 2) (hσ : σ ≠ side4 (p v)) :
    (Fintype.card V : ℝ) / 2 - 2 ≤
      (sideDeg G p v σ : ℝ) + 2 * (abnSet G p v).card + 2 := by
  have key : ∀ a b : Fin 4, AllowedT F1 (p v) a → AllowedT F1 (p v) b →
      (sideDeg G p v σ : ℝ) = degT G p v a + degT G p v b →
      (Fintype.card V : ℝ) / 2 - 2 ≤ (sideDeg G p v σ : ℝ) + 2 * (abnSet G p v).card + 2 := by
    intro a b ha hb he
    have h1 := card_clsT_le_degT_allowed G p v a ha
    have h2 := card_clsT_le_degT_allowed G p v b hb
    have h1R : ((clsT p a).card : ℝ) ≤ degT G p v a + (abnSet G p v).card + 1 := by
      exact_mod_cast h1
    have h2R : ((clsT p b).card : ℝ) ≤ degT G p v b + (abnSet G p v).card + 1 := by
      exact_mod_cast h2
    have := h.cls_lo a
    have := h.cls_lo b
    linarith
  rcases p_cases (p := p) v with hc | hc | hc | hc
  · have : σ = 1 := by
      have h2 : ∀ x : Fin 2, x ≠ side4 0 → x = 1 := by decide
      exact h2 σ (hc ▸ hσ)
    subst this
    exact key 2 3 (by rw [hc]; decide) (by rw [hc]; decide) (by rw [sideDeg_one]; push_cast; ring)
  · have : σ = 1 := by
      have h2 : ∀ x : Fin 2, x ≠ side4 1 → x = 1 := by decide
      exact h2 σ (hc ▸ hσ)
    subst this
    exact key 2 3 (by rw [hc]; decide) (by rw [hc]; decide) (by rw [sideDeg_one]; push_cast; ring)
  · have : σ = 0 := by
      have h2 : ∀ x : Fin 2, x ≠ side4 2 → x = 0 := by decide
      exact h2 σ (hc ▸ hσ)
    subst this
    exact key 0 1 (by rw [hc]; decide) (by rw [hc]; decide) (by rw [sideDeg_zero]; push_cast; ring)
  · have : σ = 0 := by
      have h2 : ∀ x : Fin 2, x ≠ side4 3 → x = 0 := by decide
      exact h2 σ (hc ▸ hσ)
    subst this
    exact key 0 1 (by rw [hc]; decide) (by rw [hc]; decide) (by rw [sideDeg_zero]; push_cast; ring)

/-- The degree of a normal vertex is at most `3n/4 + 1 + s n`. -/
lemma degree_le_normal (h : Setup126 G p A s) (v : V) (hv : v ∉ A) :
    (G.degree v : ℝ) ≤ 3 * (Fintype.card V : ℝ) / 4 + 1 + s * Fintype.card V := by
  have hsum := sum_degT_eq_degree G p v
  have hown := sideDeg_own_le (G := G) (p := p) v
  have hcl := h.cls_hi (p v)
  have hab := h.normal v hv
  have hdeg : G.degree v = sideDeg G p v 0 + sideDeg G p v 1 := by
    rw [← hsum, Fin.sum_univ_four, sideDeg_zero, sideDeg_one]; ring
  have hother : ∀ σ : Fin 2, σ ≠ side4 (p v) → (sideDeg G p v σ : ℝ) ≤
      (Fintype.card V : ℝ) - (clsT p (p v)).card - (Fintype.card V : ℝ) / 4 + 1 := by
    intro σ hσ
    have hall := sum_card_clsT p
    rw [Fin.sum_univ_four] at hall
    have hallR : ((clsT p 0).card : ℝ) + (clsT p 1).card + (clsT p 2).card + (clsT p 3).card =
        Fintype.card V := by exact_mod_cast hall
    have b0 := h.cls_lo 0
    have b1 := h.cls_lo 1
    have b2 := h.cls_lo 2
    have b3 := h.cls_lo 3
    have d0 := degT_le_class G p v 0
    have d1 := degT_le_class G p v 1
    have d2 := degT_le_class G p v 2
    have d3 := degT_le_class G p v 3
    rcases p_cases (p := p) v with hc | hc | hc | hc <;>
    · have hσv : σ = 1 - side4 (p v) := by rw [hc] at hσ ⊢; revert σ; decide
      rw [hσv, hc] at *
      first
        | (rw [show (1 : Fin 2) - side4 0 = 1 by decide, sideDeg_one]; push_cast
           have : (degT G p v 2 : ℝ) ≤ (clsT p 2).card := by exact_mod_cast d2
           have : (degT G p v 3 : ℝ) ≤ (clsT p 3).card := by exact_mod_cast d3
           linarith)
        | (rw [show (1 : Fin 2) - side4 1 = 1 by decide, sideDeg_one]; push_cast
           have : (degT G p v 2 : ℝ) ≤ (clsT p 2).card := by exact_mod_cast d2
           have : (degT G p v 3 : ℝ) ≤ (clsT p 3).card := by exact_mod_cast d3
           linarith)
        | (rw [show (1 : Fin 2) - side4 2 = 0 by decide, sideDeg_zero]; push_cast
           have : (degT G p v 0 : ℝ) ≤ (clsT p 0).card := by exact_mod_cast d0
           have : (degT G p v 1 : ℝ) ≤ (clsT p 1).card := by exact_mod_cast d1
           linarith)
        | (rw [show (1 : Fin 2) - side4 3 = 0 by decide, sideDeg_zero]; push_cast
           have : (degT G p v 0 : ℝ) ≤ (clsT p 0).card := by exact_mod_cast d0
           have : (degT G p v 1 : ℝ) ≤ (clsT p 1).card := by exact_mod_cast d1
           linarith)
  have hownR : (sideDeg G p v (side4 (p v)) : ℝ) ≤ (clsT p (p v)).card + (abnSet G p v).card := by
    exact_mod_cast hown
  have hdegR : (G.degree v : ℝ) = sideDeg G p v 0 + sideDeg G p v 1 := by exact_mod_cast hdeg
  have hs2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  rcases hs2 (side4 (p v)) with hσ | hσ
  · have := hother 1 (by rw [hσ]; decide)
    rw [hσ] at hownR
    linarith
  · have := hother 0 (by rw [hσ]; decide)
    rw [hσ] at hownR
    linarith

lemma side_cases (x : Fin 2) : x = 0 ∨ x = 1 := by revert x; decide

/-- Every vertex of large internal degree lies in `A`. -/
lemma highInt_mem_126 (h : Setup126 G p A s) (hs : s ≤ 1 / 1000)
    (hsn : 10 ≤ s * (Fintype.card V : ℝ)) (v : V)
    (hv : 0.371 * (Fintype.card V : ℝ) ≤ (partDeg G (sideP G p A) v (sideP G p A v) : ℝ)) :
    v ∈ A := by
  by_contra hvA
  have h1 := partDeg_sideP_le (G := G) (p := p) (A := A) v (sideP G p A v)
  rw [sideP_of_not_mem hvA] at h1 hv
  have h2 := sideDeg_own_le (G := G) (p := p) v
  have h1R : (partDeg G (sideP G p A) v (side4 (p v)) : ℝ) ≤
      (clsT p (p v)).card + (abnSet G p v).card + A.card := by
    exact_mod_cast h1.trans (by omega)
  have := h.cls_hi (p v)
  have := h.normal v hvA
  have := h.A_card
  nlinarith

/-- **Claim 12.6.4**: `G[P*]` is `100 s`-cross-balanced. -/
lemma crossBalanced_126 (h : Setup126 G p A s)
    (hsn : 10 ≤ s * (Fintype.card V : ℝ)) : IsCrossBalanced (100 * s) G (sideP G p A) := by
  intro v i hi
  have hA := h.A_card
  have u1 := partDeg_sideP_le (G := G) (p := p) (A := A) v (sideP G p A v)
  have u2 := sideDeg_le_partDeg (G := G) (p := p) (A := A) v i
  have u1R : (partDeg G (sideP G p A) v (sideP G p A v) : ℝ) ≤
      sideDeg G p v (sideP G p A v) + A.card := by exact_mod_cast u1
  have u2R : (sideDeg G p v i : ℝ) ≤ partDeg G (sideP G p A) v i + A.card := by
    exact_mod_cast u2
  have hs0 : 0 ≤ s := by
    have : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    by_contra hneg; push_neg at hneg; nlinarith
  by_cases hvA : v ∈ A
  · have hle := newPart_side_le (G := G) (p := p) hvA
    have key : sideDeg G p v (sideP G p A v) ≤ sideDeg G p v i := by
      unfold sideP at hi ⊢
      rcases side_cases (side4 (newPart G p A v)) with hσ | hσ
      · rw [hσ] at hi ⊢
        have : i = 1 := by rcases side_cases i with h' | h' <;> simp_all
        subst this
        rw [sideDeg_zero, sideDeg_one]; simpa [hσ] using hle
      · rw [hσ] at hi ⊢
        have : i = 0 := by rcases side_cases i with h' | h' <;> simp_all
        subst this
        rw [sideDeg_zero, sideDeg_one]; simpa [hσ] using hle
    have keyR : (sideDeg G p v (sideP G p A v) : ℝ) ≤ sideDeg G p v i := by exact_mod_cast key
    nlinarith
  · rw [sideP_of_not_mem hvA] at u1R hi ⊢
    have h2 := sideDeg_own_le (G := G) (p := p) v
    have h2R : (sideDeg G p v (side4 (p v)) : ℝ) ≤ (clsT p (p v)).card + (abnSet G p v).card := by
      exact_mod_cast h2
    have h3 := sideDeg_other_ge h v i hi
    have := h.cls_hi (p v)
    have := h.normal v hvA
    nlinarith

/-- **Claim 12.6.5**: `G[P*]` is `100 s`-extremal. -/
lemma twoExtremal_126 (h : Setup126 G p A s) (hs : s ≤ 1 / 1000)
    (hsn : 10 ≤ s * (Fintype.card V : ℝ)) : IsTwoExtremal (100 * s) G (sideP G p A) := by
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hs0 : 0 ≤ s := by by_contra hneg; push_neg at hneg; nlinarith
  have hA := h.A_card
  constructor
  · -- (i) the vertices outside `A` have small degree
    have hsub : Aᶜ ⊆ univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + 100 * s) * n) := by
      intro v hv
      simp only [mem_compl] at hv
      simp only [mem_filter, mem_univ, true_and]
      have := degree_le_normal h v hv
      nlinarith
    have h1 := card_le_card hsub
    rw [card_compl] at h1
    have h2 : (((Fintype.card V - A.card : ℕ)) : ℝ) ≤
        ((univ.filter (fun v => (G.degree v : ℝ) ≤ (3 / 4 + 100 * s) * n)).card : ℝ) := by
      exact_mod_cast h1
    have h3 : A.card ≤ Fintype.card V := card_le_univ A
    push_cast [h3] at h2
    nlinarith
  · -- (ii) the cut `P*` is large
    set q := sideP G p A with hq
    set U : Finset V := (clsT p 0 ∪ clsT p 1) \ A with hU
    have hUsub : U ⊆ partClass q 0 := by
      intro v hv
      simp only [hU, mem_sdiff, mem_union, clsT, mem_filter, mem_univ, true_and] at hv
      simp only [partClass, mem_filter, mem_univ, true_and, hq, sideP_of_not_mem hv.2]
      rcases hv.1 with h' | h' <;> rw [h'] <;> decide
    have hcut := (cutSize_eq_sum_partDeg G q).1
    have hle : ∑ v ∈ U, partDeg G q v 1 ≤ cutSize G (partClass q 0) := by
      rw [hcut]; exact sum_le_sum_of_subset hUsub
    set L : ℝ := n / 2 - 4 - 4 * s * n with hL
    have hpd : ∀ v ∈ U, L ≤ (partDeg G q v 1 : ℝ) := by
      intro v hv
      simp only [hU, mem_sdiff, mem_union, clsT, mem_filter, mem_univ, true_and] at hv
      have hσ : (1 : Fin 2) ≠ side4 (p v) := by rcases hv.1 with h' | h' <;> rw [h'] <;> decide
      have h3 := sideDeg_other_ge h v 1 hσ
      have h4 := sideDeg_le_partDeg (G := G) (p := p) (A := A) v 1
      have h4R : (sideDeg G p v 1 : ℝ) ≤ partDeg G q v 1 + A.card := by exact_mod_cast h4
      have := h.normal v hv.2
      nlinarith
    have hUc : n / 2 - 2 - 2 * s * n ≤ (U.card : ℝ) := by
      have h1 : (clsT p 0 ∪ clsT p 1).card = (clsT p 0).card + (clsT p 1).card := by
        rw [card_union_of_disjoint]
        rw [disjoint_left]; intro x h0 h1
        simp only [clsT, mem_filter, mem_univ, true_and] at h0 h1
        rw [h0] at h1; exact absurd h1 (by decide)
      have h2 : (clsT p 0 ∪ clsT p 1).card ≤ U.card + A.card := by
        rw [hU]
        calc (clsT p 0 ∪ clsT p 1).card ≤ ((clsT p 0 ∪ clsT p 1) \ A ∪ A).card :=
              card_le_card fun x hx => by
                by_cases hxA : x ∈ A
                exacts [mem_union_right _ hxA, mem_union_left _ (mem_sdiff.mpr ⟨hx, hxA⟩)]
          _ ≤ _ := card_union_le _ _
      have h2R : ((clsT p 0).card : ℝ) + (clsT p 1).card ≤ U.card + A.card := by
        rw [h1] at h2; exact_mod_cast h2
      have := h.cls_lo 0
      have := h.cls_lo 1
      linarith
    have hsumR : (U.card : ℝ) * L ≤ ((∑ v ∈ U, partDeg G q v 1 : ℕ) : ℝ) := by
      push_cast
      have := sum_le_sum hpd
      rw [sum_const, nsmul_eq_mul] at this
      linarith
    have hcutR : ((∑ v ∈ U, partDeg G q v 1 : ℕ) : ℝ) ≤ (cutSize G (partClass q 0) : ℝ) := by
      exact_mod_cast hle
    have hL0 : 0 ≤ L := by rw [hL]; nlinarith
    have hUL : L ≤ (U.card : ℝ) := by rw [hL]; nlinarith
    have : L * L ≤ (U.card : ℝ) * L := mul_le_mul_of_nonneg_right hUL hL0
    nlinarith

end

end NashWilliams18
