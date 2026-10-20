/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BernoulliBlocks
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Tactic.FieldSimp

/-! # A lower-tail bound for a genuine independent Bernoulli event family

This packages Mathlib's Hoeffding lemma and independent sub-Gaussian sum bound.
The event probabilities are actual measure values. Applying this to all typed
queries of the physical reserve, then selecting one simultaneous outcome,
remains a separate assembly obligation.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FiniteBernoulliTail

open Finset MeasureTheory ProbabilityTheory

theorem lower_half_mean {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (prob : ℝ) (hp : 0 ≤ prob) (hmarg : ∀ i, μ.real (A i) = prob) :
    μ.real {ω | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤
        prob * Fintype.card I / 2} ≤
      Real.exp (-prob ^ 2 * Fintype.card I / 2) := by
  classical
  let Z : I → Ω → ℝ := fun i => (A i).indicator (fun _ => 1)
  let Y : I → Ω → ℝ := fun i ω => prob - Z i ω
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_const.indicator (hA i)
  have hmean : ∀ i, ∫ ω, Z i ω ∂μ = prob := by
    intro i
    rw [show Z i = (A i).indicator (1 : Ω → ℝ) from rfl,
      integral_indicator_one (hA i)]
    exact hmarg i
  have hYind : iIndepFun Y μ := by
    exact hind.iIndepFun_indicator.comp (fun _ (x : ℝ) => prob - x)
      (fun _ => measurable_const.sub measurable_id)
  have hsub : ∀ i : I, HasSubgaussianMGF (Y i) (((2 : NNReal) ^ 2)⁻¹) μ := by
    intro i
    have h01 : ∀ᵐ ω ∂μ, -Z i ω ∈ Set.Icc (-1 : ℝ) 0 := by
      apply ae_of_all
      intro ω
      by_cases h : ω ∈ A i <;> simp [Z, h]
    have hs := hasSubgaussianMGF_of_mem_Icc (X := fun ω => -Z i ω)
      ((hZ i).neg.aemeasurable) h01
    have heq : (fun ω => -Z i ω - ∫ ω, -Z i ω ∂μ) = Y i := by
      funext ω
      rw [integral_neg, hmean]
      dsimp [Y]
      ring
    rw [heq] at hs
    norm_num at hs ⊢
    exact hs
  have ht : 0 ≤ prob * (Fintype.card I : ℝ) / 2 := by positivity
  have hb := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind
    (s := univ) (fun i _ => hsub i) ht
  have hevent : {ω | (∑ i, Z i ω) ≤ prob * Fintype.card I / 2} =
      {ω | prob * Fintype.card I / 2 ≤ ∑ i, Y i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Y, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  have hn : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hexponent : -(prob * (Fintype.card I : ℝ) / 2) ^ 2 /
      (2 * ∑ _i : I, (((2 : NNReal) ^ 2)⁻¹ : NNReal)) =
        -prob ^ 2 * Fintype.card I / 2 := by
    simp
    field_simp
  change μ.real {ω | (∑ i, Z i ω) ≤ prob * Fintype.card I / 2} ≤ _
  rw [hevent]
  simpa only [hexponent] using hb

end PartitionedTriangleAbsorption.FiniteBernoulliTail
