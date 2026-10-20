/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case124.Vortex.TupleStat
public import RequestProject.NW18.Case124.Vortex.SecondMoment

@[expose] public section

/-!
# One random child of a vortex level: simultaneous Hoeffding and Chebyshev control

`exists_child_discrepancy_tuple`: a `q`-random subset `U` of a level `W` satisfies, at the same
time,
* the Hoeffding discrepancy `|T κ ∩ U| = q |T κ ∩ W| ± t` for every query `κ ∈ I`, and
* the upper bound `#{s ∈ A : s ⊆ U} ≤ ∑_{s ∈ A} q^{|im s|} + c` for a family `A ⊆ W^k` of
  `k`-tuples (Chebyshev, with variance at most `k² |W|^{2k-1}`),

provided `|I| · 2 exp(-2t²/|W|) + k² |W|^{2k-1} / c² < 1`.  Everything is local to the level
`W`: the ambient vertex count never enters.
-/

namespace NashWilliams18.Vortex124

open MeasureTheory ProbabilityTheory Finset PartitionedTriangleAbsorption.L3F0
open scoped NNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- The expected count of a tuple family is at most `q^k |A|` plus the non-injective tuples. -/
lemma sum_pow_image_le (W : Finset V) {k : ℕ} (A : Finset (Fin k → V)) (hA : A ⊆ tup W k)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ s ∈ A, q ^ (univ.image s).card ≤ q ^ k * A.card + (k : ℝ) ^ 2 * (W.card : ℝ) ^ (k - 1) := by
  classical
  rw [← sum_filter_add_sum_filter_not A (fun s => Function.Injective s)]
  have h1 : ∑ s ∈ A.filter (fun s => Function.Injective s), q ^ (univ.image s).card ≤
      q ^ k * A.card := by
    have : ∀ s ∈ A.filter (fun s => Function.Injective s), q ^ (univ.image s).card = q ^ k := by
      intro s hs
      rw [card_image_of_injective _ (mem_filter.mp hs).2, card_univ, Fintype.card_fin]
    rw [sum_congr rfl this, sum_const, nsmul_eq_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast card_filter_le _ _) (pow_nonneg hq0 _)
  have h2 : ∑ s ∈ A.filter (fun s => ¬ Function.Injective s), q ^ (univ.image s).card ≤
      (k : ℝ) ^ 2 * (W.card : ℝ) ^ (k - 1) := by
    calc _ ≤ ∑ _s ∈ A.filter (fun s => ¬ Function.Injective s), (1 : ℝ) :=
          sum_le_sum fun s _ => pow_le_one₀ hq0 hq1
      _ = ((A.filter (fun s => ¬ Function.Injective s)).card : ℝ) := by simp
      _ ≤ (k : ℝ) ^ 2 * (W.card : ℝ) ^ (k - 1) := by
        have hsub : A.filter (fun s => ¬ Function.Injective s) ⊆
            ((univ ×ˢ univ : Finset (Fin k × Fin k)).filter (fun ij => ij.1 ≠ ij.2)).biUnion
              (fun ij => (tup W k).filter (fun s => s ij.1 = s ij.2)) := by
          intro s hs
          rw [mem_filter] at hs
          obtain ⟨hsA, hni⟩ := hs
          rw [Function.Injective] at hni
          push_neg at hni
          obtain ⟨i, j, hij, hne⟩ := hni
          rw [mem_biUnion]
          exact ⟨(i, j), by simp [hne], mem_filter.mpr ⟨hA hsA, hij⟩⟩
        have hc := (card_le_card hsub).trans card_biUnion_le
        have hc2 : ∑ ij ∈ (univ ×ˢ univ : Finset (Fin k × Fin k)).filter (fun ij => ij.1 ≠ ij.2),
            ((tup W k).filter (fun s => s ij.1 = s ij.2)).card ≤
            ∑ _ij ∈ (univ ×ˢ univ : Finset (Fin k × Fin k)), W.card ^ (k - 1) := by
          refine (sum_le_sum fun ij hij => card_tup_eq_le W (mem_filter.mp hij).2).trans ?_
          exact sum_le_sum_of_subset (filter_subset _ _)
        rw [sum_const, smul_eq_mul, card_product, card_univ, Fintype.card_fin] at hc2
        have := hc.trans hc2
        rw [← sq] at this
        exact_mod_cast this
  linarith

/-- **Joint Hoeffding/Chebyshev child.** -/
theorem exists_child_discrepancy_tuple {K : Type*} (W : Finset V) (q : ℝ≥0) (hq : q ≤ 1)
    (T : K → Finset V) (I : Finset K) {t : ℝ} (ht : 0 < t) (hW : 0 < W.card)
    {k : ℕ} (A : Finset (Fin k → V)) (hA : A ⊆ tup W k) {c : ℝ} (hc : 0 < c)
    (hsmall : (I.card : ℝ) * (2 * Real.exp (-2 * t ^ 2 / W.card)) +
      (k : ℝ) ^ 2 * (W.card : ℝ) ^ (2 * k - 1) / c ^ 2 < 1) :
    ∃ U ⊆ W, (∀ κ ∈ I, |((T κ ∩ U).card : ℝ) - q * (T κ ∩ W).card| < t) ∧
      ((A.filter (fun s => ∀ l, s l ∈ U)).card : ℝ) ≤
        ∑ s ∈ A, (q : ℝ) ^ (univ.image s).card + c := by
  classical
  set w : V → ℝ≥0 := fun v => if v ∈ W then q else 0 with hwdef
  have hw : ∀ v, w v ≤ 1 := fun v => by
    simp only [hwdef]; split_ifs
    · exact hq
    · exact zero_le_one
  set μ := bernPi w hw
  have hm : (0 : ℝ) < W.card := by exact_mod_cast hW
  set bad : K → Set (V → Bool) := fun κ =>
    {ω | t ≤ |∑ y ∈ T κ ∩ W, blockInd {y} ω - ∑ y ∈ T κ ∩ W, ∏ i ∈ ({y} : Finset V), (w i : ℝ)|}
    with hbad
  set cheb : Set (V → Bool) :=
    {ω | c ≤ |∑ s ∈ A, blockInd (univ.image s) ω - ∑ s ∈ A, ∏ i ∈ univ.image s, (w i : ℝ)|}
    with hcheb
  have hb : ∀ κ ∈ I, μ.real (bad κ) ≤ 2 * Real.exp (-2 * t ^ 2 / W.card) := by
    intro κ _
    refine tail_blocks w hw (fun y => {y}) (T κ ∩ W) ?_ ht hm ?_
    · intro y _ y' _ hyy'
      exact disjoint_singleton.mpr hyy'
    · exact_mod_cast card_le_card inter_subset_right
  have hch : μ.real cheb ≤ (k : ℝ) ^ 2 * (W.card : ℝ) ^ (2 * k - 1) / c ^ 2 := by
    refine (blockStat_chebyshev w hw A (fun s => univ.image s) hc).trans ?_
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hsub : (A ×ˢ A).filter (fun ab => ¬ Disjoint (univ.image ab.1) (univ.image ab.2)) ⊆
        (tup W k ×ˢ tup W k).filter (fun st => ∃ i j, st.1 i = st.2 j) := by
      intro ab hab
      rw [mem_filter, mem_product] at hab
      rw [mem_filter, mem_product]
      refine ⟨⟨hA hab.1.1, hA hab.1.2⟩, ?_⟩
      obtain ⟨x, hx1, hx2⟩ := not_disjoint_iff.mp hab.2
      obtain ⟨i, -, hi⟩ := mem_image.mp hx1
      obtain ⟨j, -, hj⟩ := mem_image.mp hx2
      exact ⟨i, j, hi.trans hj.symm⟩
    exact_mod_cast (card_le_card hsub).trans (card_pairs_meet_le W k)
  have hsum : μ.real ((⋃ κ ∈ I, bad κ) ∪ cheb) < 1 := by
    calc μ.real ((⋃ κ ∈ I, bad κ) ∪ cheb) ≤ μ.real (⋃ κ ∈ I, bad κ) + μ.real cheb :=
          measureReal_union_le _ _
      _ ≤ ∑ κ ∈ I, μ.real (bad κ) + μ.real cheb := by
          gcongr; exact measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _κ ∈ I, 2 * Real.exp (-2 * t ^ 2 / W.card) +
          (k : ℝ) ^ 2 * (W.card : ℝ) ^ (2 * k - 1) / c ^ 2 := by
          gcongr with κ hκ
          exact hb κ hκ
      _ < 1 := by rw [sum_const, nsmul_eq_mul]; exact hsmall
  have hne : ((⋃ κ ∈ I, bad κ) ∪ cheb) ≠ Set.univ := by
    intro h; rw [h, measureReal_def, measure_univ, ENNReal.toReal_one] at hsum
    exact lt_irrefl _ hsum
  obtain ⟨ω, hω⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  rw [Set.mem_union, not_or] at hω
  obtain ⟨hω1, hω2⟩ := hω
  refine ⟨W.filter fun v => ω v = true, filter_subset _ _, fun κ hκ => ?_, ?_⟩
  · have hnot : ¬ t ≤ |∑ y ∈ T κ ∩ W, blockInd {y} ω -
        ∑ y ∈ T κ ∩ W, ∏ i ∈ ({y} : Finset V), (w i : ℝ)| := fun h =>
      hω1 (Set.mem_biUnion hκ (by simpa only [hbad, Set.mem_setOf_eq] using h))
    have h1 : ∑ y ∈ T κ ∩ W, blockInd {y} ω =
        ((T κ ∩ W.filter fun v => ω v = true).card : ℝ) := by
      have : T κ ∩ W.filter (fun v => ω v = true) = (T κ ∩ W).filter fun v => ω v = true := by
        ext v; simp [and_assoc]
      rw [this, card_filter, Nat.cast_sum]
      refine sum_congr rfl fun y _ => ?_
      unfold blockInd
      simp only [mem_singleton, forall_eq]
      split_ifs <;> simp
    have h2 : ∑ y ∈ T κ ∩ W, ∏ i ∈ ({y} : Finset V), (w i : ℝ) = q * (T κ ∩ W).card := by
      rw [mul_comm, ← nsmul_eq_mul, ← sum_const]
      refine sum_congr rfl fun y hy => ?_
      rw [prod_singleton, hwdef]
      simp [(mem_inter.mp hy).2]
    rw [h1, h2] at hnot
    exact lt_of_not_ge hnot
  · have hnot : ¬ c ≤ |∑ s ∈ A, blockInd (univ.image s) ω -
        ∑ s ∈ A, ∏ i ∈ univ.image s, (w i : ℝ)| := fun h =>
      hω2 (by simpa only [hcheb, Set.mem_setOf_eq] using h)
    have h1 : ∑ s ∈ A, blockInd (univ.image s) ω =
        ((A.filter (fun s => ∀ l, s l ∈ W.filter fun v => ω v = true)).card : ℝ) := by
      rw [card_filter, Nat.cast_sum]
      refine sum_congr rfl fun s hs => ?_
      have hsW := mem_tup.mp (hA hs)
      unfold blockInd
      have hiff : (∀ i ∈ univ.image s, ω i = true) ↔
          ∀ l, s l ∈ W.filter fun v => ω v = true := by
        simp only [mem_image, mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff,
          mem_filter]
        exact ⟨fun h l => ⟨hsW l, h l⟩, fun h l => (h l).2⟩
      by_cases h : ∀ i ∈ univ.image s, ω i = true
      · rw [if_pos h, if_pos (hiff.mp h)]; simp
      · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; simp
    have h2 : ∑ s ∈ A, ∏ i ∈ univ.image s, (w i : ℝ) = ∑ s ∈ A, (q : ℝ) ^ (univ.image s).card := by
      refine sum_congr rfl fun s hs => ?_
      have hsW := mem_tup.mp (hA hs)
      rw [prod_congr rfl (g := fun _ => (q : ℝ)) (fun i hi => by
        obtain ⟨l, -, rfl⟩ := mem_image.mp hi
        simp [hwdef, hsW l]), prod_const]
    rw [h1, h2] at hnot
    linarith [(abs_lt.mp (lt_of_not_ge hnot)).2]

end NashWilliams18.Vortex124
