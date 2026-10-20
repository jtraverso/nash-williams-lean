/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FiniteBernoulliTail

/-! # Upper deviations of actual independent Bernoulli events

This is the upper-tail counterpart of the accepted Stage-12 lower tail.
No independence between different graph-star or common-neighbour queries is
required; independence is needed only within each individual query.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.FiniteBernoulliUpperTail

open Finset MeasureTheory ProbabilityTheory

theorem upper_deviation {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (prob gap : ℝ) (hgap : 0 ≤ gap) (hmarg : ∀ i, μ.real (A i) = prob) :
    μ.real {ω | prob * Fintype.card I + gap ≤
        ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω} ≤
      Real.exp (-2 * gap ^ 2 / Fintype.card I) := by
  classical
  let Z : I → Ω → ℝ := fun i => (A i).indicator (fun _ => 1)
  let Y : I → Ω → ℝ := fun i ω => Z i ω - prob
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_const.indicator (hA i)
  have hmean : ∀ i, ∫ ω, Z i ω ∂μ = prob := by
    intro i
    rw [show Z i = (A i).indicator (1 : Ω → ℝ) from rfl,
      integral_indicator_one (hA i)]
    exact hmarg i
  have hYind : iIndepFun Y μ :=
    hind.iIndepFun_indicator.comp (fun _ (x : ℝ) => x - prob)
      (fun _ => measurable_id.sub measurable_const)
  have hsub : ∀ i : I, HasSubgaussianMGF (Y i) (((2 : NNReal) ^ 2)⁻¹) μ := by
    intro i
    have h01 : ∀ᵐ ω ∂μ, Z i ω ∈ Set.Icc (0 : ℝ) 1 := by
      apply ae_of_all
      intro ω
      by_cases h : ω ∈ A i <;> simp [Z, h]
    have hs := hasSubgaussianMGF_of_mem_Icc (hZ i).aemeasurable h01
    simpa only [hmean, show ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : NNReal) =
      ((2 : NNReal) ^ 2)⁻¹ by norm_num] using hs
  have hb := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind
    (s := univ) (fun i _ => hsub i) hgap
  have hevent : {ω | prob * Fintype.card I + gap ≤ ∑ i, Z i ω} =
      {ω | gap ≤ ∑ i, Y i ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Y, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    constructor <;> intro h <;> linarith
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexponent : -gap ^ 2 /
      (2 * ∑ _i : I, (((2 : NNReal) ^ 2)⁻¹ : NNReal)) =
        -2 * gap ^ 2 / Fintype.card I := by
    simp
    field_simp
  change μ.real {ω | prob * Fintype.card I + gap ≤ ∑ i, Z i ω} ≤ _
  rw [hevent]
  simpa only [hexponent] using hb

end PartitionedTriangleAbsorption.FiniteBernoulliUpperTail
