/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalReserveTails

/-! # Lower tails for signed, disjoint trial blocks

A clean reserve query requires one triangle to be retained and its connector
owners to be absent. Complement events, not extra independent coins, encode
the absences.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedTrialsStage123

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks

theorem independent_signed {E Ω : Type*} [MeasurableSpace Ω]
    (A : E → Set Ω) (μ : Measure Ω) (hind : iIndepSet A μ) (sign : E → Bool) :
    iIndepSet (fun e => if sign e then A e else (A e)ᶜ) μ := by
  rw [iIndepSet_iff_iIndep] at hind ⊢
  apply iIndep_of_iIndep_of_le hind
  intro e
  apply MeasurableSpace.generateFrom_le
  intro s hs
  obtain rfl := Set.mem_singleton_iff.mp hs
  have h : MeasurableSet[MeasurableSpace.generateFrom {A e}] (A e) :=
    MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _)
  split
  · exact h
  · exact h.compl

/-- Unequal marginals are allowed; only a common lower bound is required. -/
theorem lower_half_bound {I Ω : Type*} [Fintype I] [Nonempty I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hind : iIndepSet A μ)
    (prob : ℝ) (hp : 0 ≤ prob) (hmarg : ∀ i, prob ≤ μ.real (A i)) :
    μ.real {ω | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤
      prob * Fintype.card I / 2} ≤ Real.exp (-prob ^ 2 * Fintype.card I / 2) := by
  classical
  let Z : I → Ω → ℝ := fun i => (A i).indicator (fun _ => 1)
  let Y : I → Ω → ℝ := fun i ω => μ.real (A i) - Z i ω
  have hZ : ∀ i, Measurable (Z i) := fun i => measurable_const.indicator (hA i)
  have hmean : ∀ i, ∫ ω, Z i ω ∂μ = μ.real (A i) := by
    intro i
    exact integral_indicator_one (hA i)
  have hYind : iIndepFun Y μ :=
    hind.iIndepFun_indicator.comp (fun i (x : ℝ) => μ.real (A i) - x)
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
  have hsum : prob * Fintype.card I ≤ ∑ i, μ.real (A i) := by
    simpa [mul_comm] using sum_le_sum (s := (univ : Finset I)) (fun i _ => hmarg i)
  have hset : {ω | (∑ i, Z i ω) ≤ prob * Fintype.card I / 2} ⊆
      {ω | prob * Fintype.card I / 2 ≤ ∑ i, Y i ω} := by
    intro ω hω
    change _ ≤ _ at hω ⊢
    simp only [Y, sum_sub_distrib]
    linarith
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hexponent : -(prob * (Fintype.card I : ℝ) / 2) ^ 2 /
      (2 * ∑ _i : I, (((2 : NNReal) ^ 2)⁻¹ : NNReal)) =
      -prob ^ 2 * Fintype.card I / 2 := by
    simp
    field_simp
  exact (measureReal_mono hset).trans (by simpa only [hexponent] using hb)

theorem signed_fair_marginal {E : Type*} (μ : Measure (E → Bool)) [IsProbabilityMeasure μ]
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal (1 / 2)) (sign : E → Bool) (e : E) :
    μ (if sign e then {ω | ω e = true} else {ω | ω e = true}ᶜ) =
      ENNReal.ofReal (1 / 2) := by
  split
  · exact hmarg e
  · have he : MeasurableSet {ω : E → Bool | ω e = true} :=
      (measurable_pi_apply e : Measurable (fun ω : E → Bool => ω e))
        (measurableSet_singleton (true : Bool))
    rw [measure_compl he
      (measure_ne_top _ _), measure_univ, hmarg e]
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num

/-- Signed patterns on disjoint blocks of at most three coordinates have
probability at least 1/8, and hence a uniform exponential lower tail. -/
theorem signed_blocks_tail {E I : Type*} [Fintype I] [Nonempty I]
    (μ : Measure (E → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal (1 / 2))
    (sign : E → Bool) (B : I → Finset E)
    (hdis : Pairwise (fun i j => Disjoint (B i) (B j))) (hsize : ∀ i, (B i).card ≤ 3) :
    let A := fun i => blockEvent
      (fun e => if sign e then {ω | ω e = true} else {ω | ω e = true}ᶜ) (B i)
    μ.real {ω | (∑ i, (A i).indicator (fun _ => (1 : ℝ)) ω) ≤
      (Fintype.card I : ℝ) / 16} ≤ Real.exp (-(Fintype.card I : ℝ) / 128) := by
  classical
  let S := fun e => if sign e then {ω : E → Bool | ω e = true} else {ω | ω e = true}ᶜ
  have hS : ∀ e, MeasurableSet (S e) := by
    intro e
    have h : MeasurableSet {ω : E → Bool | ω e = true} :=
      (measurable_pi_apply e : Measurable (fun ω : E → Bool => ω e))
        (measurableSet_singleton (true : Bool))
    dsimp [S]
    split
    · exact h
    · exact h.compl
  have hsi := independent_signed (fun e => {ω : E → Bool | ω e = true}) μ hind sign
  have hp : ∀ i, (1 / 8 : ℝ) ≤ μ.real (blockEvent S (B i)) := by
    intro i
    rw [measureReal_def, block_probability S μ hsi _ (signed_fair_marginal μ hmarg sign),
      ENNReal.toReal_pow, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hh := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (hsize i)
    norm_num at hh
    exact hh
  have ht := lower_half_bound μ (fun i => blockEvent S (B i))
    (fun i => blockEvent_measurable S hS (B i))
    (independent_blocks S μ hS hsi B hdis) (1 / 8) (by norm_num) hp
  have he1 : (1 / 8 : ℝ) * Fintype.card I / 2 = (Fintype.card I : ℝ) / 16 := by ring
  have he2 : -(1 / 8 : ℝ) ^ 2 * Fintype.card I / 2 = -(Fintype.card I : ℝ) / 128 := by ring
  simpa only [he1, he2] using ht

end PartitionedTriangleAbsorption.SignedTrialsStage123
