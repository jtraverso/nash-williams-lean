/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalEdgeModes

@[expose] public section

/-! # The full physical inverse on zero-row demands for F₁ and F₂ -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

def f1ZeroRowWeight (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 2 g a b c + internalPairWeight p 1 2 g a b c +
  internalPairWeight p 2 0 g a b c + internalPairWeight p 3 0 g a b c +
  repeatedPairWeight p 0 2 g a b c + repeatedPairWeight p 0 3 g a b c +
  repeatedPairWeight p 1 2 g a b c + repeatedPairWeight p 1 3 g a b c

def f2ZeroRowWeight (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  internalPairWeight p 0 2 g a b c + internalPairWeight p 1 2 g a b c +
  repeatedPairWeight p 0 2 g a b c + repeatedPairWeight p 0 3 g a b c +
  repeatedPairWeight p 1 2 g a b c + repeatedPairWeight p 1 3 g a b c +
  tripartitePairWeight p 2 3 0 g a b c

theorem f1ZeroRowWeight_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (f1ZeroRowWeight p g) := by
  unfold f1ZeroRowWeight
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | apply TernarySymmetric.add

theorem f2ZeroRowWeight_symmetric (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) : TernarySymmetric (f2ZeroRowWeight p g) := by
  unfold f2ZeroRowWeight
  repeat' first
    | exact internalPairWeight_symmetric p _ _ g hs
    | exact repeatedPairWeight_symmetric p _ _ g
    | exact abcLift_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem f1ZeroRowWeight_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p F1 (f1ZeroRowWeight p g) := by
  unfold f1ZeroRowWeight
  repeat' first
    | exact aabLift_supported p F1 _ _ (by decide) (by unfold Link; decide) _
    | apply TernarySupported.add

theorem f2ZeroRowWeight_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p F2 (f2ZeroRowWeight p g) := by
  unfold f2ZeroRowWeight
  repeat' first
    | exact aabLift_supported p F2 _ _ (by decide) (by unfold Link; decide) _
    | exact abcLift_supported p F2 _ _ _ (by decide) (by decide) (by decide) (by unfold Link; decide) _
    | apply TernarySupported.add

theorem f1ZeroRowWeight_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link F1 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (f1ZeroRowWeight p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  unfold f1ZeroRowWeight
  simp only [ternaryLoad_add, hint, hrep]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link; decide)).symm

theorem f2ZeroRowWeight_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g) (hd : ∀ a, g a a = 0)
    (hsup : ∀ a b, (¬ ∃ k, Link F2 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a b : V) :
    ternaryLoad (f2ZeroRowWeight p g) a b = g a b := by
  have hint := fun i j a b => internalPairWeight_load p i j g hr hd (hm j) a b
  have hrep := fun i j a b => repeatedPairWeight_load p i j g hs hr (hm2 i) a b
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  unfold f2ZeroRowWeight
  simp only [ternaryLoad_add, hint, hrep, htri]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link; decide)).symm

theorem edgeMode_bounds (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    (∀ i j, |internalPairWeight p i j g a b c| ≤ 12 * ε / δ) ∧
    (∀ i j, |repeatedPairWeight p i j g a b c| ≤ 12 * ε / δ) ∧
    (∀ i j k, |tripartitePairWeight p i j k g a b c| ≤ 12 * ε / δ) := by
  have hδpos : 0 < δ := by linarith
  have hpos (i : Fin 4) : 0 < classSize p i := lt_of_lt_of_le hδpos (hm i)
  have hpos2 (i : Fin 4) : 0 < classSize p i - 2 := by have := hm i; linarith
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply (internalPairWeight_bound p i j g ε hε hg (hpos j) a b c).trans
    rw [div_le_div_iff₀ (hpos j) hδpos]
    nlinarith [mul_nonneg hε (sub_nonneg.mpr (hm j)), mul_nonneg hε hδpos.le]
  · intro i j
    apply (repeatedPairWeight_bound p i j g ε hε hg (hpos2 i) a b c).trans
    rw [div_le_div_iff₀ (hpos2 i) hδpos]
    have hh : 0 ≤ 2 * classSize p i - δ - 4 := by have := hm i; linarith
    nlinarith [mul_nonneg hε hh]
  · intro i j k
    apply (tripartitePairWeight_bound p i j k g ε hε hg (hpos k) a b c).trans
    rw [div_le_div_iff₀ (hpos k) hδpos]
    nlinarith [mul_nonneg hε (sub_nonneg.mpr (hm k)), mul_nonneg hε hδpos.le]

private theorem abs_sum_eight {x0 x1 x2 x3 x4 x5 x6 x7 M : ℝ}
    (h0 : |x0| ≤ M) (h1 : |x1| ≤ M) (h2 : |x2| ≤ M) (h3 : |x3| ≤ M)
    (h4 : |x4| ≤ M) (h5 : |x5| ≤ M) (h6 : |x6| ≤ M) (h7 : |x7| ≤ M) :
    |x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7| ≤ 8 * M := by
  rw [abs_le] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
  constructor <;> linarith

theorem f1ZeroRowWeight_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f1ZeroRowWeight p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, _⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h := abs_sum_eight (hi 0 2) (hi 1 2) (hi 2 0) (hi 3 0)
    (hr 0 2) (hr 0 3) (hr 1 2) (hr 1 3)
  calc
    _ ≤ 8 * (12 * ε / δ) := h
    _ = 96 * ε / δ := by ring

theorem f2ZeroRowWeight_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f2ZeroRowWeight p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨hi, hr, ht⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have hM : |(0 : ℝ)| ≤ 12 * ε / δ := by rw [abs_zero]; positivity
  have h := abs_sum_eight (hi 0 2) (hi 1 2) (hr 0 2) (hr 0 3)
    (hr 1 2) (hr 1 3) (ht 2 3 0) hM
  simp only [add_zero] at h
  calc
    _ ≤ 8 * (12 * ε / δ) := h
    _ = 96 * ε / δ := by ring

#print axioms f1ZeroRowWeight_symmetric
#print axioms f2ZeroRowWeight_symmetric
#print axioms f1ZeroRowWeight_supported
#print axioms f2ZeroRowWeight_supported
#print axioms f1ZeroRowWeight_load
#print axioms f2ZeroRowWeight_load
#print axioms f1ZeroRowWeight_bound
#print axioms f2ZeroRowWeight_bound

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
