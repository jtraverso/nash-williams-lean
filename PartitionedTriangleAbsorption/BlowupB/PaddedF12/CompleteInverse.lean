/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.CompleteResiduals

@[expose] public section

/-! # A bounded signed inverse on every complete allowed F₁/F₂ blowup

The construction first corrects all class totals, next all vertex-to-class rows,
and finally the residual with every class row zero.
-/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

theorem exists_complete_inverse_of_stages (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (g : V → V → ℝ)
    (ε M0 M1 M2 ε1 ε2 : ℝ) (hε1 : 0 ≤ ε1)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p F g) (hg : ∀ a b, |g a b| ≤ ε)
    (hstep1 : ε + (Fintype.card V : ℝ) * M0 ≤ ε1)
    (hstep2 : ε1 + (Fintype.card V : ℝ) * M1 ≤ ε2)
    (htype : ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p F w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧ ∀ a b c, |w a b c| ≤ M0)
    (hvertex : ∀ d : V → Fin 4 → ℝ, VertexDemandZero p d →
      VertexDemandSupported p F d → (∀ a i, |d a i| ≤ (Fintype.card V : ℝ) * ε1) →
      ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
        (∀ a i, classRow p (ternaryLoad w) a i = d a i) ∧ ∀ a b c, |w a b c| ≤ M1)
    (hzero : ∀ f : V → V → ℝ, (∀ a b, f a b = f b a) → (∀ a, f a a = 0) →
      EdgeSupported p F f → ClassRowsZero p f → (∀ a b, |f a b| ≤ ε2) →
      ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
        (∀ a b, ternaryLoad w a b = f a b) ∧ ∀ a b c, |w a b c| ≤ M2) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧ ∀ a b c, |w a b c| ≤ M0 + M1 + M2 := by
  obtain ⟨w0, hsym0, hsup0, htot0, hb0⟩ := htype
  let g1 := fun a b => g a b - ternaryLoad w0 a b
  have hsym1 : ∀ a b, g1 a b = g1 b a := by
    intro a b
    dsimp only [g1]
    rw [hsym a b, hsym0.load_symmetric a b]
  have hd1 : ∀ a, g1 a a = 0 := by
    intro a
    dsimp only [g1]
    rw [hd a, hsup0.load_diag a, sub_self]
  have hs1 : EdgeSupported p F g1 := hs.sub hsup0.edgeSupported
  have hb1 : ∀ a b, |g1 a b| ≤ ε1 := fun a b =>
    (residual_bound g w0 ε M0 hg hb0 a b).trans hstep1
  obtain ⟨w1, hsymw1, hsupw1, hrow1, hbw1⟩ :=
    hvertex (classRow p g1) (residual_vertexDemandZero p g _ htot0) hs1.rows
      (classRow_bound p g1 ε1 hε1 hb1)
  let g2 := fun a b => g1 a b - ternaryLoad w1 a b
  have hsym2 : ∀ a b, g2 a b = g2 b a := by
    intro a b
    dsimp only [g2]
    rw [hsym1 a b, hsymw1.load_symmetric a b]
  have hd2 : ∀ a, g2 a a = 0 := by
    intro a
    dsimp only [g2]
    rw [hd1 a, hsupw1.load_diag a, sub_self]
  have hs2 : EdgeSupported p F g2 := hs1.sub hsupw1.edgeSupported
  have hr2 : ClassRowsZero p g2 := residual_classRowsZero p g1 _ hrow1
  have hb2 : ∀ a b, |g2 a b| ≤ ε2 := fun a b =>
    (residual_bound g1 w1 ε1 M1 hb1 hbw1 a b).trans hstep2
  obtain ⟨w2, hsymw2, hsupw2, hload2, hbw2⟩ := hzero g2 hsym2 hd2 hs2 hr2 hb2
  refine ⟨fun a b c => w0 a b c + w1 a b c + w2 a b c,
    (hsym0.add hsymw1).add hsymw2, (hsup0.add hsupw1).add hsupw2, ?_, ?_⟩
  · intro a b
    rw [ternaryLoad_add, ternaryLoad_add, hload2]
    dsimp only [g2, g1]
    ring
  · intro a b c
    exact (abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add (hb0 a b c) (hbw1 a b c))) (hbw2 a b c))

theorem complete_inverse_budgets (ε γ n : ℝ) (hε : 0 ≤ ε)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hn : 0 < n) :
    (ε + n * (32 * ε / (γ ^ 3 * n)) ≤ 33 * ε / γ ^ 3) ∧
    (33 * ε / γ ^ 3 + n * (9504 * ε / (γ ^ 5 * n)) ≤ 9537 * ε / γ ^ 5) ∧
    (32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) +
      915552 * ε / (γ ^ 6 * n) ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * n)) := by
  have hg2 : γ ^ 2 ≤ 1 := pow_le_one₀ hγ.le hγ1
  have hg3 : γ ^ 3 ≤ 1 := pow_le_one₀ hγ.le hγ1
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have h3 : 0 < γ ^ 3 := pow_pos hγ _
  have h5 : 0 < γ ^ 5 := pow_pos hγ _
  have h6 : 0 < γ ^ 6 * n := mul_pos (pow_pos hγ _) hn
  refine ⟨?_, ?_, ?_⟩
  · apply (le_div_iff₀ h3).mpr
    field_simp [hγ0, hn0]
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hg3)]
  · apply (le_div_iff₀ h5).mpr
    field_simp [hγ0, hn0]
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hg2)]
  · apply (le_div_iff₀ h6).mpr
    field_simp [hγ0, hn0]
    norm_num
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hg3),
      mul_nonneg hε (sub_nonneg.mpr hγ1)]

theorem exists_complete_inverse_F12 (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p F g) (hg : ∀ a b, |g a b| ≤ ε)
    (hfamily : (F = F1 ∧ F1RealCompatible p g) ∨ (F = F2 ∧ F2RealCompatible p g)) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    exact (mul_pos_iff_of_pos_left hγ).mp (lt_of_lt_of_le (by norm_num) hlarge)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hε1 : 0 ≤ 33 * ε / γ ^ 3 := by positivity
  have hε2 : 0 ≤ 9537 * ε / γ ^ 5 := by positivity
  have hm (i : Fin 4) : classSize p i ≠ 0 := by have := hmin i; linarith
  have hm1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hmin i; linarith
  have hm2 (i : Fin 4) : classSize p i - 2 ≠ 0 := by have := hmin i; linarith
  obtain ⟨hstep1, hstep2, hbudget⟩ := complete_inverse_budgets ε γ n hε hγ hγ1 hn
  have he0 : 32 * (ε * n ^ 2) / (γ * n) ^ 3 = 32 * ε / (γ ^ 3 * n) := by
    field_simp [hγ0, hn0]
  have he1 : 288 * (n * (33 * ε / γ ^ 3)) / (γ * n) ^ 2 =
      9504 * ε / (γ ^ 5 * n) := by
    field_simp [hγ0, hn0]
    ring
  have he2 : 96 * (9537 * ε / γ ^ 5) / (γ * n) = 915552 * ε / (γ ^ 6 * n) := by
    field_simp [hγ0, hn0]
    ring
  have hstage : ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p F w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p F g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · rcases hfamily with ⟨rfl, hc⟩ | ⟨rfl, hc⟩
      · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_F1 p g (ε * n ^ 2)
          (γ * n) (by positivity) hlarge hmin hsym hs hc (classTotal_bound p g ε hε hg)
        exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
      · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_F2 p g (ε * n ^ 2)
          (γ * n) (by positivity) hlarge hmin hsym hs hc (classTotal_bound p g ε hε hg)
        exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      rcases hfamily with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · refine ⟨f1VertexWeight p d, f1VertexWeight_symmetric p d,
          f1VertexWeight_supported p d, f1VertexWeight_rows p d hz hds hm hm1 hm2, ?_⟩
        intro a b c
        exact he1 ▸ f1VertexWeight_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
          (by positivity) hlarge hdb hmin a b c
      · refine ⟨f2VertexWeight p d, f2VertexWeight_symmetric p d,
          f2VertexWeight_supported p d, f2VertexWeight_rows p d hz hds hm hm1 hm2, ?_⟩
        intro a b c
        exact he1 ▸ f2VertexWeight_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
          (by positivity) hlarge hdb hmin a b c
    · intro f hf hfd hfs hr hb
      rcases hfamily with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · refine ⟨f1ZeroRowWeight p f, f1ZeroRowWeight_symmetric p f hf,
          f1ZeroRowWeight_supported p f, f1ZeroRowWeight_load p f hf hr hfd hfs hm hm2, ?_⟩
        intro a b c
        exact he2 ▸ f1ZeroRowWeight_bound p f (9537 * ε / γ ^ 5) (γ * n)
          hε2 hlarge hb hmin a b c
      · refine ⟨f2ZeroRowWeight p f, f2ZeroRowWeight_symmetric p f hf,
          f2ZeroRowWeight_supported p f, f2ZeroRowWeight_load p f hf hr hfd hfs hm hm2, ?_⟩
        intro a b c
        exact he2 ▸ f2ZeroRowWeight_bound p f (9537 * ε / γ ^ 5) (γ * n)
          hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

theorem exists_complete_inverse_F1 (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p F1 g) (hg : ∀ a b, |g a b| ≤ ε)
    (hcompat : F1RealCompatible p g) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F1 w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) :=
  exists_complete_inverse_F12 p F1 g ε γ hε hγ hγ1 hlarge hmin hsym hd hs hg
    (Or.inl ⟨rfl, hcompat⟩)

theorem exists_complete_inverse_F2 (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p F2 g) (hg : ∀ a b, |g a b| ≤ ε)
    (hcompat : F2RealCompatible p g) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F2 w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) :=
  exists_complete_inverse_F12 p F2 g ε γ hε hγ hγ1 hlarge hmin hsym hd hs hg
    (Or.inr ⟨rfl, hcompat⟩)

#print axioms exists_complete_inverse_of_stages
#print axioms complete_inverse_budgets
#print axioms exists_complete_inverse_F12
#print axioms exists_complete_inverse_F1
#print axioms exists_complete_inverse_F2

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
