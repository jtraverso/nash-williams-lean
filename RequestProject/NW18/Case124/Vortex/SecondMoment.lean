/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.L3F0Hoeffding

/-!
# Second moment of block statistics under a product Bernoulli measure

For a finite family of blocks `B a` (`a ∈ A`) of independent bits, the statistic
`X = ∑_{a ∈ A} 1[all bits of B a are 1]` has variance at most the number of ordered pairs
`(a, b) ∈ A × A` whose blocks meet (disjoint blocks are independent).  Chebyshev's inequality
then bounds the deviation probability.
-/

namespace NashWilliams18.Vortex124

open MeasureTheory ProbabilityTheory Finset PartitionedTriangleAbsorption.L3F0
open scoped NNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma blockInd_mul_blockInd (A B : Finset ι) (ω : ι → Bool) :
    blockInd A ω * blockInd B ω = blockInd (A ∪ B) ω := by
  unfold blockInd
  simp only [forall_mem_union]
  by_cases hA : ∀ i ∈ A, ω i = true <;> by_cases hB : ∀ i ∈ B, ω i = true
  · rw [if_pos hA, if_pos hB, if_pos ⟨hA, hB⟩, mul_one]
  · rw [if_pos hA, if_neg hB, if_neg (fun h => hB h.2), mul_zero]
  · rw [if_neg hA, zero_mul, if_neg (show ¬(_ ∧ _) from fun h => hA h.1)]
  · rw [if_neg hA, zero_mul, if_neg (show ¬(_ ∧ _) from fun h => hA h.1)]

variable {α : Type*}

/-- **Second moment of a block statistic.** -/
theorem blockStat_var_le (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) (A : Finset α) (B : α → Finset ι) :
    ∫ ω, (∑ a ∈ A, blockInd (B a) ω - ∑ a ∈ A, ∏ i ∈ B a, (w i : ℝ)) ^ 2 ∂(bernPi w hw) ≤
      ((A ×ˢ A).filter (fun ab => ¬ Disjoint (B ab.1) (B ab.2))).card := by
  classical
  set μ := bernPi w hw
  set m : α → ℝ := fun a => ∏ i ∈ B a, (w i : ℝ) with hm
  have hint : ∀ f : (ι → Bool) → ℝ, Integrable f μ := fun f => Integrable.of_finite
  have hE : ∀ a, ∫ ω, blockInd (B a) ω ∂μ = m a := fun a => integral_blockInd w hw (B a)
  have hexp : ∀ ω, (∑ a ∈ A, blockInd (B a) ω - ∑ a ∈ A, m a) ^ 2 =
      ∑ ab ∈ A ×ˢ A, (blockInd (B ab.1 ∪ B ab.2) ω - m ab.1 * blockInd (B ab.2) ω -
        m ab.2 * blockInd (B ab.1) ω + m ab.1 * m ab.2) := by
    intro ω
    rw [← sum_sub_distrib, sq, sum_mul_sum, ← sum_product']
    refine sum_congr rfl fun ab _ => ?_
    rw [← blockInd_mul_blockInd]; ring
  simp_rw [hexp]
  rw [integral_finset_sum _ (fun _ _ => hint _)]
  have hterm : ∀ ab ∈ A ×ˢ A, ∫ ω, (blockInd (B ab.1 ∪ B ab.2) ω - m ab.1 * blockInd (B ab.2) ω -
        m ab.2 * blockInd (B ab.1) ω + m ab.1 * m ab.2) ∂μ =
      ∫ ω, blockInd (B ab.1 ∪ B ab.2) ω ∂μ - m ab.1 * m ab.2 := by
    intro ab _
    rw [integral_add (hint _) (hint _), integral_sub (hint _) (hint _),
      integral_sub (hint _) (hint _), integral_const_mul, integral_const_mul, hE, hE,
      integral_const, probReal_univ, one_smul]
    ring
  rw [sum_congr rfl hterm]
  rw [← sum_filter_add_sum_filter_not (A ×ˢ A) (fun ab => ¬ Disjoint (B ab.1) (B ab.2))]
  have hdisj : ∑ ab ∈ (A ×ˢ A).filter (fun ab => ¬ ¬ Disjoint (B ab.1) (B ab.2)),
      (∫ ω, blockInd (B ab.1 ∪ B ab.2) ω ∂μ - m ab.1 * m ab.2) = 0 := by
    refine sum_eq_zero fun ab hab => ?_
    have hd : Disjoint (B ab.1) (B ab.2) := not_not.mp (mem_filter.mp hab).2
    rw [integral_blockInd, prod_union hd]
    simp [hm]
  rw [hdisj, add_zero]
  calc ∑ ab ∈ (A ×ˢ A).filter (fun ab => ¬ Disjoint (B ab.1) (B ab.2)),
        (∫ ω, blockInd (B ab.1 ∪ B ab.2) ω ∂μ - m ab.1 * m ab.2)
      ≤ ∑ _ab ∈ (A ×ˢ A).filter (fun ab => ¬ Disjoint (B ab.1) (B ab.2)), (1 : ℝ) := by
        refine sum_le_sum fun ab _ => ?_
        rw [integral_blockInd]
        have h1 : ∏ i ∈ B ab.1 ∪ B ab.2, (w i : ℝ) ≤ 1 := by
          exact_mod_cast (Finset.prod_le_one (s := B ab.1 ∪ B ab.2) (fun i _ => hw i))
        have h2 : 0 ≤ m ab.1 * m ab.2 :=
          mul_nonneg (prod_nonneg fun i _ => NNReal.coe_nonneg _)
            (prod_nonneg fun i _ => NNReal.coe_nonneg _)
        linarith
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_one]

/-- **Chebyshev for a block statistic.** -/
theorem blockStat_chebyshev (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) (A : Finset α) (B : α → Finset ι)
    {c : ℝ} (hc : 0 < c) :
    (bernPi w hw).real {ω | c ≤ |∑ a ∈ A, blockInd (B a) ω - ∑ a ∈ A, ∏ i ∈ B a, (w i : ℝ)|} ≤
      ((A ×ˢ A).filter (fun ab => ¬ Disjoint (B ab.1) (B ab.2))).card / c ^ 2 := by
  set μ := bernPi w hw
  set f : (ι → Bool) → ℝ :=
    fun ω => (∑ a ∈ A, blockInd (B a) ω - ∑ a ∈ A, ∏ i ∈ B a, (w i : ℝ)) ^ 2
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _) Integrable.of_finite (c ^ 2)
  have hvar := blockStat_var_le w hw A B
  have hsub : {ω | c ≤ |∑ a ∈ A, blockInd (B a) ω - ∑ a ∈ A, ∏ i ∈ B a, (w i : ℝ)|} ⊆
      {ω | c ^ 2 ≤ f ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have := pow_le_pow_left₀ hc.le hω 2
    rwa [sq_abs] at this
  have hmono := measureReal_mono (μ := μ) hsub
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg c]

end NashWilliams18.Vortex124
