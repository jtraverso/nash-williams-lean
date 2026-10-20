/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Hoeffding's inequality for indicator variables of disjoint blocks of independent bits

`Ω = ι → Bool` carries the product of Bernoulli measures with parameters `w i`. For a family of
pairwise disjoint finite blocks `B y` (`y ∈ Y`), the indicators `Z_y = 1[all bits in B y are 1]`
are independent; Hoeffding's inequality (from Mathlib) bounds the deviation of their sum.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.L3F0

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The product Bernoulli measure. -/
noncomputable def bernPi (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) : Measure (ι → Bool) :=
  Measure.pi fun i => (PMF.bernoulli (w i) (hw i)).toMeasure

instance (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) : IsProbabilityMeasure (bernPi w hw) := by
  unfold bernPi; infer_instance

/-- Indicator that all bits of `B` are `true`. -/
noncomputable def blockInd (B : Finset ι) (ω : ι → Bool) : ℝ :=
  if ∀ i ∈ B, ω i = true then 1 else 0

theorem blockInd_mem_Icc (B : Finset ι) (ω : ι → Bool) : blockInd B ω ∈ Set.Icc (0 : ℝ) 1 := by
  unfold blockInd; split_ifs <;> simp

omit [DecidableEq ι] in
theorem coord_iIndep (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) :
    iIndepFun (fun i (ω : ι → Bool) => ω i) (bernPi w hw) := by
  unfold bernPi
  exact iIndepFun_pi (X := fun _ b => b) (fun _ => measurable_id.aemeasurable)

theorem integral_blockInd (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) (B : Finset ι) :
    (bernPi w hw)[blockInd B] = ∏ i ∈ B, (w i : ℝ) := by
  classical
  have hset : {ω : ι → Bool | ∀ i ∈ B, ω i = true} =
      Set.pi Set.univ (fun i => if i ∈ B then {true} else Set.univ) := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h i; split_ifs with hi
      · exact h i hi
      · trivial
    · intro h i hi; have := h i; rw [if_pos hi] at this; exact this
  have hind : blockInd B =
      Set.indicator {ω : ι → Bool | ∀ i ∈ B, ω i = true} (fun _ => (1 : ℝ)) := by
    funext ω; unfold blockInd; simp [Set.indicator]
  rw [hind, integral_indicator_const _ (MeasurableSet.of_discrete), smul_eq_mul, mul_one, hset,
    measureReal_def, bernPi, Measure.pi_pi, ENNReal.toReal_prod]
  have hfac : ∀ i, (((PMF.bernoulli (w i) (hw i)).toMeasure
      (if i ∈ B then {true} else Set.univ)).toReal) = if i ∈ B then (w i : ℝ) else 1 := by
    intro i
    split_ifs with hi
    · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.bernoulli_apply]
      simp
    · rw [measure_univ]; simp
  rw [Finset.prod_congr rfl (fun i _ => hfac i), Finset.prod_ite_mem, Finset.univ_inter]

theorem blockInd_congr {B : Finset ι} {ω ω' : ι → Bool} (h : ∀ i ∈ B, ω i = ω' i) :
    blockInd B ω = blockInd B ω' := by
  unfold blockInd
  congr 1
  apply propext
  constructor
  · intro h' i hi; rw [← h i hi]; exact h' i hi
  · intro h' i hi; rw [h i hi]; exact h' i hi

/-- Extension of a partial assignment by `true`. -/
def extBits (T : Finset ι) (x : T → Bool) : ι → Bool :=
  fun i => if h : i ∈ T then x ⟨i, h⟩ else true

omit [Fintype ι] in
theorem extBits_restrict (T : Finset ι) (ω : ι → Bool) {i : ι} (hi : i ∈ T) :
    extBits T (fun j : T => ω j) i = ω i := by
  simp [extBits, hi]

/-- The centred sum of block indicators over pairwise disjoint blocks is sub-Gaussian with
parameter `|Y| / 4`. -/
theorem subG_blocks (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) {β : Type*}
    (B : β → Finset ι) (Y : Finset β)
    (hdisj : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → Disjoint (B y) (B y')) :
    HasSubgaussianMGF (fun ω => ∑ y ∈ Y, (blockInd (B y) ω - (bernPi w hw)[blockInd (B y)]))
      (∑ _y ∈ Y, (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (bernPi w hw) := by
  classical
  induction Y using Finset.induction_on with
  | empty => simp
  | insert a Y ha ih =>
    have ih' := ih (fun y hy y' hy' hne => hdisj y (Finset.mem_insert_of_mem hy) y'
      (Finset.mem_insert_of_mem hy') hne)
    set μ := bernPi w hw
    set E : β → ℝ := fun y => μ[blockInd (B y)]
    have h1 : HasSubgaussianMGF (fun ω => blockInd (B a) ω - E a) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ :=
      hasSubgaussianMGF_of_mem_Icc (measurable_of_finite _).aemeasurable
        (ae_of_all _ (blockInd_mem_Icc _))
    set T := Y.biUnion B
    have hdT : Disjoint (B a) T := by
      rw [Finset.disjoint_biUnion_right]
      intro y hy
      exact hdisj a (Finset.mem_insert_self _ _) y (Finset.mem_insert_of_mem hy)
        (fun h => ha (h ▸ hy))
    have hind := (coord_iIndep w hw).indepFun_finset (B a) T hdT (fun i => measurable_pi_apply i)
    have hind2 := hind.comp
      (measurable_of_finite (fun x : B a → Bool => blockInd (B a) (extBits (B a) x) - E a))
      (measurable_of_finite (fun x : T → Bool =>
        ∑ y ∈ Y, (blockInd (B y) (extBits T x) - E y)))
    have e1 : ((fun x : B a → Bool => blockInd (B a) (extBits (B a) x) - E a) ∘
        fun ω (i : B a) => ω i) = fun ω => blockInd (B a) ω - E a := by
      funext ω
      simp only [Function.comp]
      rw [blockInd_congr (fun i hi => extBits_restrict (B a) ω hi)]
    have e2 : ((fun x : T → Bool => ∑ y ∈ Y, (blockInd (B y) (extBits T x) - E y)) ∘
        fun ω (i : T) => ω i) = fun ω => ∑ y ∈ Y, (blockInd (B y) ω - E y) := by
      funext ω
      simp only [Function.comp]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [blockInd_congr (fun i hi => extBits_restrict T ω
        (Finset.mem_biUnion.mpr ⟨y, hy, hi⟩))]
    rw [e1, e2] at hind2
    have := h1.add_of_indepFun ih' hind2
    rw [Finset.sum_insert ha]
    convert this using 2 with ω
    rw [Finset.sum_insert ha]

/-- **Two-sided Hoeffding bound** for block indicators. -/
theorem tail_blocks (w : ι → ℝ≥0) (hw : ∀ i, w i ≤ 1) {β : Type*}
    (B : β → Finset ι) (Y : Finset β)
    (hdisj : ∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → Disjoint (B y) (B y')) {t m : ℝ} (ht : 0 < t)
    (hm : 0 < m) (hY : (Y.card : ℝ) ≤ m) :
    (bernPi w hw).real {ω | t ≤ |∑ y ∈ Y, blockInd (B y) ω - ∑ y ∈ Y, ∏ i ∈ B y, (w i : ℝ)|} ≤
      2 * Real.exp (-2 * t ^ 2 / m) := by
  classical
  set μ := bernPi w hw
  have h := subG_blocks w hw B Y hdisj
  set X : (ι → Bool) → ℝ := fun ω => ∑ y ∈ Y, (blockInd (B y) ω - μ[blockInd (B y)]) with hX
  have hXeq : ∀ ω, ∑ y ∈ Y, blockInd (B y) ω - ∑ y ∈ Y, ∏ i ∈ B y, (w i : ℝ) = X ω := by
    intro ω
    simp only [hX, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_congr rfl (fun y _ => (integral_blockInd w hw (B y)).symm)
  simp_rw [hXeq]
  rcases Nat.eq_zero_or_pos Y.card with h0 | h0
  · have hY : Y = ∅ := Finset.card_eq_zero.mp h0
    have : {ω | t ≤ |X ω|} = ∅ := by
      ext ω; simp only [hX, hY, Finset.sum_empty, abs_zero, Set.mem_setOf_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      exact ht
    rw [this, measureReal_empty]; positivity
  have hc : ((∑ _y ∈ Y, (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = Y.card / 4 := by
    simp; ring
  have hexp : Real.exp (-t ^ 2 / (2 * ((∑ _y ∈ Y, (‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) : ℝ))) ≤
      Real.exp (-2 * t ^ 2 / m) := by
    rw [hc]
    apply Real.exp_le_exp.mpr
    have hY0 : (0 : ℝ) < Y.card := by exact_mod_cast h0
    rw [show -t ^ 2 / (2 * ((Y.card : ℝ) / 4)) = -2 * t ^ 2 / Y.card by field_simp; ring]
    rw [div_le_div_iff₀ hY0 hm]
    nlinarith [sq_nonneg t]
  have hsub : {ω | t ≤ |X ω|} ⊆ {ω | t ≤ X ω} ∪ {ω | t ≤ (-X) ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union, Pi.neg_apply] at hω ⊢
    rcases le_abs'.mp hω with h1 | h1
    · right; linarith
    · left; exact h1
  calc μ.real {ω | t ≤ |X ω|} ≤ μ.real ({ω | t ≤ X ω} ∪ {ω | t ≤ (-X) ω}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | t ≤ X ω} + μ.real {ω | t ≤ (-X) ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-2 * t ^ 2 / m) + Real.exp (-2 * t ^ 2 / m) := by
        gcongr
        · exact (h.measure_ge_le ht.le).trans hexp
        · exact (h.neg.measure_ge_le ht.le).trans hexp
    _ = 2 * Real.exp (-2 * t ^ 2 / m) := by ring

end PartitionedTriangleAbsorption.L3F0
