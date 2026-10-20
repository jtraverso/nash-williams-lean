/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SelfExcludingReserveStage123

/-! # Two-sided count control on the same coins as the reserve queries -/

@[expose] public section

namespace PartitionedTriangleAbsorption.BalancedTrialsStage126

open Finset MeasureTheory ProbabilityTheory

theorem lower_deviation {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (prob gap : ℝ) (hgap : 0 ≤ gap) (hmarg : ∀ i, μ.real (A i) = prob) :
    μ.real {ω | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤
        prob * Fintype.card I - gap} ≤
      Real.exp (-2 * gap ^ 2 / Fintype.card I) := by
  classical
  let Z : I → Ω → ℝ := fun i => (A i).indicator (fun _ => 1)
  let Y : I → Ω → ℝ := fun i ω => prob - Z i ω
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_const.indicator (hA i)
  have hmean : ∀ i, ∫ ω, Z i ω ∂μ = prob := by
    intro i
    rw [show Z i = (A i).indicator (1 : Ω → ℝ) from rfl,
      integral_indicator_one (hA i)]
    exact hmarg i
  have hYind : iIndepFun Y μ := hind.iIndepFun_indicator.comp
    (fun _ (x : ℝ) => prob - x) (fun _ => measurable_const.sub measurable_id)
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
  have hb := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hYind
    (s := univ) (fun i _ => hsub i) hgap
  have hevent : {ω | (∑ i, Z i ω) ≤ prob * Fintype.card I - gap} =
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
  change μ.real {ω | (∑ i, Z i ω) ≤ prob * Fintype.card I - gap} ≤ _
  rw [hevent]
  simpa only [hexponent] using hb

theorem two_sided_deviation {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (prob gap : ℝ) (hgap : 0 ≤ gap) (hmarg : ∀ i, μ.real (A i) = prob) :
    μ.real {ω | gap < |(∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) -
        prob * Fintype.card I|} ≤ 2 * Real.exp (-2 * gap ^ 2 / Fintype.card I) := by
  let X := fun ω => ∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω
  let L := {ω | X ω ≤ prob * Fintype.card I - gap}
  let U := {ω | prob * Fintype.card I + gap ≤ X ω}
  have hsub : {ω | gap < |X ω - prob * Fintype.card I|} ⊆ L ∪ U := by
    intro ω hω
    change gap < |X ω - prob * Fintype.card I| at hω
    rcases lt_abs.mp hω with h | h
    · right; change _ ≤ _; linarith
    · left; change _ ≤ _; linarith
  have hl := lower_deviation μ A hA hind prob gap hgap hmarg
  have hu := FiniteBernoulliUpperTail.upper_deviation μ A hA hind prob gap hgap hmarg
  exact (measureReal_mono hsub).trans ((measureReal_union_le L U).trans (by
    change μ.real L + μ.real U ≤ _
    change μ.real L ≤ _ at hl
    change μ.real U ≤ _ at hu
    linarith))

theorem fair_finset_tail {I : Type*}
    (μ : Measure (I → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun i => {ω | ω i = true}) μ)
    (hmarg : ∀ i, μ {ω | ω i = true} = ENNReal.ofReal (1 / 2))
    (S : Finset I) (hS : S.Nonempty) (t : ℝ) (ht : 0 ≤ t) :
    μ.real {ω | t < |((S.filter fun i => ω i = true).card : ℝ) -
        (S.card : ℝ) / 2|} ≤ 2 * Real.exp (-2 * t ^ 2 / S.card) := by
  classical
  let J := {i // i ∈ S}
  have : Nonempty J := by obtain ⟨i, hi⟩ := hS; exact ⟨⟨i, hi⟩⟩
  let A : J → Set (I → Bool) := fun i => {ω | ω i.val = true}
  have hA : ∀ i, MeasurableSet (A i) := by
    intro i
    exact measurableSet_eq_fun (measurable_pi_apply i.val) measurable_const
  have hi : iIndepSet A μ := hind.precomp Subtype.val_injective
  have hm : ∀ i, μ.real (A i) = (1 / 2 : ℝ) := by
    intro i
    rw [measureReal_def, hmarg i.val, ENNReal.toReal_ofReal (by norm_num)]
  have hs : ∀ ω, (∑ i : J, (A i).indicator (fun _ => (1 : ℝ)) ω) =
      ((S.filter fun i => ω i = true).card : ℝ) := by
    intro ω
    calc
      _ = ∑ i ∈ S, if ω i = true then (1 : ℝ) else 0 := by
        apply sum_bij (fun i _ => i.val)
        · intro i _; exact i.property
        · intro i _ j _ h; exact Subtype.ext h
        · intro i hi; exact ⟨⟨i, hi⟩, mem_univ _, rfl⟩
        · intro i _; simp only [A, Set.indicator_apply, Set.mem_ofPred_eq]
      _ = _ := by simp only [sum_boole]
  have hc : Fintype.card J = S.card := Fintype.card_coe _
  simpa only [hs, hc, one_div, mul_comm (2⁻¹ : ℝ), ← div_eq_mul_inv] using
    two_sided_deviation μ A hA hi (1 / 2) t ht hm

end PartitionedTriangleAbsorption.BalancedTrialsStage126
