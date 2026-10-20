/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.L3F0Hoeffding

/-! # Random vertex subsets: simultaneous discrepancy for a family of test sets

The probabilistic core of the vortex (R3). A `β`-random subset `U'` of a finite set `U` meets
each of a family of test sets `T k` in `β |T k ∩ U| ± t`, simultaneously for all `k ∈ I`, as soon
as `|I| · 2 exp(-2t²/|U|) < 1`. Test sets are deterministic: in the vortex they are the rooted
common neighbourhoods of the pristine reserve (roots in `U`), the classes of `U`, and the
`X`-neighbourhoods of vertices of `U`. Uniformity in the later `L ⊆ X` is NOT obtained by a union
bound over `L`: only the neighbourhoods of `X` itself are tested.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.L3F0

open MeasureTheory ProbabilityTheory Finset
open scoped NNReal ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Simultaneous discrepancy of a random subset.** -/
theorem exists_subset_discrepancy {K : Type*} (U : Finset V) (β : ℝ≥0) (hβ : β ≤ 1)
    (T : K → Finset V) (I : Finset K) {t : ℝ} (ht : 0 < t) (hU : 0 < U.card)
    (hsmall : (I.card : ℝ) * (2 * Real.exp (-2 * t ^ 2 / U.card)) < 1) :
    ∃ U' ⊆ U, ∀ k ∈ I, |((T k ∩ U').card : ℝ) - β * (T k ∩ U).card| < t := by
  classical
  set w : V → ℝ≥0 := fun v => if v ∈ U then β else 0 with hwdef
  have hw : ∀ v, w v ≤ 1 := fun v => by
    simp only [hwdef]; split_ifs
    · exact hβ
    · exact zero_le_one
  set μ := bernPi w hw
  set b := 2 * Real.exp (-2 * t ^ 2 / U.card)
  set bad : K → Set (V → Bool) := fun k =>
    {ω | t ≤ |∑ y ∈ T k ∩ U, blockInd {y} ω - ∑ y ∈ T k ∩ U, ∏ i ∈ ({y} : Finset V), (w i : ℝ)|}
    with hbad
  have hm : (0 : ℝ) < U.card := by exact_mod_cast hU
  have hb : ∀ k ∈ I, μ.real (bad k) ≤ b := by
    intro k _
    refine tail_blocks w hw (fun y => {y}) (T k ∩ U) ?_ ht hm ?_
    · intro y _ y' _ hyy'
      exact disjoint_singleton.mpr hyy'
    · exact_mod_cast card_le_card inter_subset_right
  have hsum : μ.real (⋃ k ∈ I, bad k) < 1 := by
    calc μ.real (⋃ k ∈ I, bad k) ≤ ∑ k ∈ I, μ.real (bad k) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ I, b := sum_le_sum hb
      _ = I.card * b := by rw [sum_const, nsmul_eq_mul]
      _ < 1 := hsmall
  have hne : (⋃ k ∈ I, bad k) ≠ Set.univ := by
    intro h; rw [h, measureReal_def, measure_univ, ENNReal.toReal_one] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨U.filter fun v => ω v = true, filter_subset _ _, fun k hk => ?_⟩
  have hnot : ¬ t ≤ |∑ y ∈ T k ∩ U, blockInd {y} ω -
      ∑ y ∈ T k ∩ U, ∏ i ∈ ({y} : Finset V), (w i : ℝ)| := fun h =>
    hω (Set.mem_biUnion hk (by simpa only [hbad, Set.mem_setOf_eq] using h))
  have h1 : ∑ y ∈ T k ∩ U, blockInd {y} ω = ((T k ∩ U.filter fun v => ω v = true).card : ℝ) := by
    have : T k ∩ U.filter (fun v => ω v = true) = (T k ∩ U).filter fun v => ω v = true := by
      ext v; simp [and_assoc]
    rw [this, card_filter, Nat.cast_sum]
    refine sum_congr rfl fun y _ => ?_
    unfold blockInd
    simp only [mem_singleton, forall_eq]
    split_ifs <;> simp
  have h2 : ∑ y ∈ T k ∩ U, ∏ i ∈ ({y} : Finset V), (w i : ℝ) = β * (T k ∩ U).card := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun y hy => ?_
    rw [prod_singleton, hwdef]
    simp [(mem_inter.mp hy).2]
  rw [h1, h2] at hnot
  exact lt_of_not_ge hnot

/-- **Simultaneous discrepancy with per-test tolerances.** Each test set `T k` is allowed its own
tolerance `t k` and variance proxy `m k ≥ |T k ∩ U|`. -/
theorem exists_subset_discrepancy' {K : Type*} (U : Finset V) (β : ℝ≥0) (hβ : β ≤ 1)
    (T : K → Finset V) (I : Finset K) (t m : K → ℝ) (ht : ∀ k ∈ I, 0 < t k)
    (hm : ∀ k ∈ I, 0 < m k) (hTm : ∀ k ∈ I, ((T k ∩ U).card : ℝ) ≤ m k)
    (hsmall : ∑ k ∈ I, 2 * Real.exp (-2 * t k ^ 2 / m k) < 1) :
    ∃ U' ⊆ U, ∀ k ∈ I, |((T k ∩ U').card : ℝ) - β * (T k ∩ U).card| < t k := by
  classical
  set w : V → ℝ≥0 := fun v => if v ∈ U then β else 0 with hwdef
  have hw : ∀ v, w v ≤ 1 := fun v => by
    simp only [hwdef]; split_ifs
    · exact hβ
    · exact zero_le_one
  set μ := bernPi w hw
  set bad : K → Set (V → Bool) := fun k =>
    {ω | t k ≤ |∑ y ∈ T k ∩ U, blockInd {y} ω -
      ∑ y ∈ T k ∩ U, ∏ i ∈ ({y} : Finset V), (w i : ℝ)|} with hbad
  have hb : ∀ k ∈ I, μ.real (bad k) ≤ 2 * Real.exp (-2 * t k ^ 2 / m k) := by
    intro k hk
    refine tail_blocks w hw (fun y => {y}) (T k ∩ U) ?_ (ht k hk) (hm k hk) (hTm k hk)
    intro y _ y' _ hyy'
    exact disjoint_singleton.mpr hyy'
  have hsum : μ.real (⋃ k ∈ I, bad k) < 1 := by
    calc μ.real (⋃ k ∈ I, bad k) ≤ ∑ k ∈ I, μ.real (bad k) := measureReal_biUnion_finset_le _ _
      _ ≤ ∑ k ∈ I, 2 * Real.exp (-2 * t k ^ 2 / m k) := sum_le_sum hb
      _ < 1 := hsmall
  have hne : (⋃ k ∈ I, bad k) ≠ Set.univ := by
    intro h; rw [h, measureReal_def, measure_univ, ENNReal.toReal_one] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  refine ⟨U.filter fun v => ω v = true, filter_subset _ _, fun k hk => ?_⟩
  have hnot : ¬ t k ≤ |∑ y ∈ T k ∩ U, blockInd {y} ω -
      ∑ y ∈ T k ∩ U, ∏ i ∈ ({y} : Finset V), (w i : ℝ)| := fun h =>
    hω (Set.mem_biUnion hk (by simpa only [hbad, Set.mem_setOf_eq] using h))
  have h1 : ∑ y ∈ T k ∩ U, blockInd {y} ω = ((T k ∩ U.filter fun v => ω v = true).card : ℝ) := by
    have : T k ∩ U.filter (fun v => ω v = true) = (T k ∩ U).filter fun v => ω v = true := by
      ext v; simp [and_assoc]
    rw [this, card_filter, Nat.cast_sum]
    refine sum_congr rfl fun y _ => ?_
    unfold blockInd
    simp only [mem_singleton, forall_eq]
    split_ifs <;> simp
  have h2 : ∑ y ∈ T k ∩ U, ∏ i ∈ ({y} : Finset V), (w i : ℝ) = β * (T k ∩ U).card := by
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
    refine sum_congr rfl fun y hy => ?_
    rw [prod_singleton, hwdef]
    simp [(mem_inter.mp hy).2]
  rw [h1, h2] at hnot
  exact lt_of_not_ge hnot

end PartitionedTriangleAbsorption.L3F0
