/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.ValueLemma

@[expose] public section

/-!
# The greedy four-colouring of a nearly extremal thin weighting (Claim 8.10.1)

For a triangle-thin `K₅`-free `[0,1]`-weighting `a` of a finite set `S` (`ThinWeights S a`) we
repeatedly pick a vertex `v` of maximum weighted degree among the remaining vertices and split
off its non-neighbours.  After four rounds nothing is left (the four chosen vertices together
with a fifth remaining one would be a positive `K₅`), and every class `X` satisfies
`∑_{x,y ∈ X} a x y ≤ |S|²/2 - ∑_{x,y ∈ S} a x y`: otherwise replacing the class by weighted
clones of its chosen vertex would beat the value lemma.
-/

namespace NashWilliams.Frac

open Finset

variable {α : Type*} [DecidableEq α]

/-- Block sum `∑_{x ∈ A} ∑_{y ∈ B} a x y`. -/
def bsum (a : α → α → ℝ) (A B : Finset α) : ℝ := ∑ x ∈ A, ∑ y ∈ B, a x y

lemma value_bound {S : Finset α} {a : α → α → ℝ} (H : ThinWeights S a) :
    bsum a S S ≤ (S.card : ℝ) ^ 2 / 2 := by
  have hv := value_lemma S a H (fun _ => 1) (fun _ => zero_le_one)
  simp only [quadF, mul_one, sum_const, nsmul_eq_mul] at hv
  simpa [bsum] using hv

omit [DecidableEq α] in
lemma bsum_comm {a : α → α → ℝ} (hs : ∀ i j, a i j = a j i) (A B : Finset α) :
    bsum a A B = bsum a B A := by
  unfold bsum; rw [sum_comm]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => hs _ _

lemma bsum_sdiff_left (a : α → α → ℝ) {X S : Finset α} (h : X ⊆ S) (B : Finset α) :
    bsum a (S \ X) B = bsum a S B - bsum a X B := by
  unfold bsum; rw [← sum_sdiff h]; ring

section step

variable {S : Finset α} {a : α → α → ℝ}

/-- The modified weighting in which the class `X` is replaced by clones of `v`. -/
def cloneW (a : α → α → ℝ) (X : Finset α) (v : α) (x y : α) : ℝ :=
  if x ∈ X then (if y ∈ X then 0 else a v y) else (if y ∈ X then a x v else a x y)

lemma thin_cloneW (H : ThinWeights S a) {X : Finset α} {v : α} (hvS : v ∈ S) (hvX : v ∈ X) :
    ThinWeights S (cloneW a X v) where
  symm := by
    intro i j; unfold cloneW
    by_cases hi : i ∈ X <;> by_cases hj : j ∈ X <;> simp [hi, hj, H.symm]
  diag := by intro i; unfold cloneW; by_cases hi : i ∈ X <;> simp [hi, H.diag]
  nonneg := by
    intro i j; unfold cloneW
    split_ifs <;> first | exact le_rfl | exact H.nonneg _ _
  le_one := by
    intro i j; unfold cloneW
    split_ifs <;> first | exact zero_le_one | exact H.le_one _ _
  thin := by
    intro i hi j hj k hk hij hik hjk
    unfold cloneW
    have b := H.le_one
    have z := H.nonneg
    by_cases ai : i ∈ X <;> by_cases aj : j ∈ X <;> by_cases ak : k ∈ X <;>
      simp only [ai, aj, ak, if_true, if_false]
    all_goals first
      | (norm_num; done)
      | linarith [b v j, b v k, b j v, b k v, b i v, b v i]
      | exact H.thin v hvS j hj k hk (fun h => aj (h ▸ hvX)) (fun h => ak (h ▸ hvX)) hjk
      | exact H.thin i hi v hvS k hk (fun h => ai (h ▸ hvX)) hik (fun h => ak (h ▸ hvX))
      | exact H.thin i hi j hj v hvS hij (fun h => ai (h ▸ hvX)) (fun h => aj (h ▸ hvX))
      | exact H.thin i hi j hj k hk hij hik hjk
  clique := by
    intro T hTS hT
    -- at most one element of `T` lies in `X`
    by_cases hX : ∃ x ∈ T, x ∈ X
    · obtain ⟨x, hxT, hxX⟩ := hX
      have hone : ∀ y ∈ T, y ≠ x → y ∉ X := by
        intro y hy hyx hyX
        have := hT x hxT y hy (Ne.symm hyx)
        simp [cloneW, hxX, hyX] at this
      set T' := insert v (T.erase x)
      have hvT : v ∉ T.erase x := by
        intro h
        exact hone v (mem_of_mem_erase h) (ne_of_mem_erase h) hvX
      have hcard : T'.card = T.card := by
        rw [card_insert_of_notMem hvT, card_erase_of_mem hxT]
        have : 0 < T.card := card_pos.2 ⟨x, hxT⟩
        omega
      rw [← hcard]
      apply H.clique
      · intro y hy
        rcases mem_insert.1 hy with rfl | hy
        · exact hvS
        · exact hTS (mem_of_mem_erase hy)
      · intro p hp q hq hpq
        have key : ∀ y ∈ T.erase x, 0 < a v y := by
          intro y hy
          have hyX := hone y (mem_of_mem_erase hy) (ne_of_mem_erase hy)
          have := hT x hxT y (mem_of_mem_erase hy) (Ne.symm (ne_of_mem_erase hy))
          simpa [cloneW, hxX, hyX] using this
        rcases mem_insert.1 hp with hp' | hp' <;> rcases mem_insert.1 hq with hq' | hq'
        · exact absurd (hp'.trans hq'.symm) hpq
        · rw [hp']; exact key q hq'
        · rw [hq', H.symm]; exact key p hp'
        · have hp := hp'
          have hq := hq'
          have hpX := hone p (mem_of_mem_erase hp) (ne_of_mem_erase hp)
          have hqX := hone q (mem_of_mem_erase hq) (ne_of_mem_erase hq)
          have := hT p (mem_of_mem_erase hp) q (mem_of_mem_erase hq) hpq
          simpa [cloneW, hpX, hqX] using this
    · push_neg at hX
      apply H.clique T hTS
      intro p hp q hq hpq
      have := hT p hp q hq hpq
      simpa [cloneW, hX p hp, hX q hq] using this

/-- The weighted degree. -/
def wdeg (S : Finset α) (a : α → α → ℝ) (x : α) : ℝ := ∑ y ∈ S, a x y

lemma bsum_cloneW (H : ThinWeights S a) {X : Finset α} {v : α} (hXS : X ⊆ S)
    (hv0 : ∀ y ∈ X, a v y = 0) :
    bsum (cloneW a X v) S S = bsum a S S + bsum a X X +
      2 * ((X.card : ℝ) * wdeg S a v - ∑ x ∈ X, wdeg S a x) := by
  -- row sums of the modified weighting
  have rowX : ∀ x ∈ X, ∑ y ∈ S, cloneW a X v x y = wdeg S a v := by
    intro x hx
    unfold cloneW wdeg
    simp only [hx, if_true]
    rw [← sum_sdiff hXS]
    have h1 : ∑ y ∈ X, (if y ∈ X then (0:ℝ) else a v y) = 0 :=
      sum_eq_zero fun y hy => by simp [hy]
    have h2 : ∑ y ∈ S \ X, (if y ∈ X then (0:ℝ) else a v y) = ∑ y ∈ S \ X, a v y :=
      sum_congr rfl fun y hy => by simp [(mem_sdiff.1 hy).2]
    have h3 : ∑ y ∈ X, a v y = 0 := sum_eq_zero hv0
    rw [h1, h2, ← sum_sdiff hXS (f := fun y => a v y), h3]
  have rowN : ∀ x ∈ S \ X, ∑ y ∈ S, cloneW a X v x y =
      (X.card : ℝ) * a x v + (wdeg S a x - ∑ y ∈ X, a x y) := by
    intro x hx
    have hxX := (mem_sdiff.1 hx).2
    unfold cloneW wdeg
    simp only [hxX, if_false]
    rw [← sum_sdiff hXS]
    have h1 : ∑ y ∈ X, (if y ∈ X then a x v else a x y) = X.card * a x v := by
      rw [sum_congr rfl fun y hy => if_pos hy, sum_const, nsmul_eq_mul]
    have h2 : ∑ y ∈ S \ X, (if y ∈ X then a x v else a x y) = ∑ y ∈ S \ X, a x y :=
      sum_congr rfl fun y hy => by simp [(mem_sdiff.1 hy).2]
    rw [h1, h2, ← sum_sdiff hXS (f := fun y => a x y)]
    ring
  have hsplit : bsum (cloneW a X v) S S = ∑ x ∈ S \ X, ∑ y ∈ S, cloneW a X v x y +
      ∑ x ∈ X, ∑ y ∈ S, cloneW a X v x y := by
    unfold bsum; rw [sum_sdiff hXS]
  rw [hsplit, sum_congr rfl rowX, sum_congr rfl rowN, sum_const, nsmul_eq_mul,
    sum_add_distrib, sum_sub_distrib, ← mul_sum]
  -- the three remaining sums
  have e1 : ∑ x ∈ S \ X, a x v = wdeg S a v := by
    rw [sum_sdiff_eq_sub hXS]
    have : ∑ x ∈ X, a x v = 0 := sum_eq_zero fun x hx => by rw [H.symm]; exact hv0 x hx
    rw [this, sub_zero]; unfold wdeg
    exact sum_congr rfl fun y _ => H.symm _ _
  have e2 : ∑ x ∈ S \ X, wdeg S a x = bsum a S S - ∑ x ∈ X, wdeg S a x := by
    rw [sum_sdiff_eq_sub hXS]; rfl
  have e3 : ∑ x ∈ S \ X, ∑ y ∈ X, a x y = ∑ x ∈ X, wdeg S a x - bsum a X X := by
    have := bsum_sdiff_left a hXS X
    unfold bsum at this; rw [this]
    have h4 : ∑ x ∈ S, ∑ y ∈ X, a x y = ∑ x ∈ X, wdeg S a x := by
      have := bsum_comm H.symm S X; unfold bsum at this; rw [this]; rfl
    rw [h4]; rfl
  rw [e1, e2, e3]
  ring

/-- **One greedy step (Claim 8.10.1).** -/
lemma greedy_step (H : ThinWeights S a) {T : Finset α} (hTS : T ⊆ S) (hT : T.Nonempty) :
    ∃ v ∈ T, bsum a (T.filter fun y => ¬ 0 < a v y) (T.filter fun y => ¬ 0 < a v y) ≤
      (S.card : ℝ) ^ 2 / 2 - bsum a S S := by
  obtain ⟨v, hvT, hmax⟩ := exists_max_image T (wdeg S a) hT
  refine ⟨v, hvT, ?_⟩
  set X := T.filter fun y => ¬ 0 < a v y
  have hXS : X ⊆ S := (filter_subset _ _).trans hTS
  have hvX : v ∈ X := mem_filter.2 ⟨hvT, by rw [H.diag]; exact lt_irrefl 0⟩
  have hv0 : ∀ y ∈ X, a v y = 0 := fun y hy =>
    le_antisymm (not_lt.1 (mem_filter.1 hy).2) (H.nonneg _ _)
  have hb := bsum_cloneW H hXS hv0
  have hval := value_bound (thin_cloneW H (hTS hvT) hvX)
  have hdeg : ∑ x ∈ X, wdeg S a x ≤ (X.card : ℝ) * wdeg S a v := by
    calc ∑ x ∈ X, wdeg S a x ≤ ∑ x ∈ X, wdeg S a v :=
          sum_le_sum fun x hx => hmax x (mem_filter.1 hx).1
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  linarith

end step

/-- **The greedy partition.**  A triangle-thin `K₅`-free weighting of `S` admits a partition of
`S` into four classes, each of inner weight at most `|S|²/2 - ∑_{x,y ∈ S} a x y`. -/
theorem greedy_partition {S : Finset α} {a : α → α → ℝ} (H : ThinWeights S a) :
    ∃ X : Fin 4 → Finset α, (∀ i, X i ⊆ S) ∧ (∀ i j, i ≠ j → Disjoint (X i) (X j)) ∧
      (∀ x ∈ S, ∃ i, x ∈ X i) ∧
      ∀ i, bsum a (X i) (X i) ≤ (S.card : ℝ) ^ 2 / 2 - bsum a S S := by
  classical
  -- one step, packaged so that it can be iterated
  have step : ∀ T ⊆ S, ∃ Y R : Finset α, Y ⊆ T ∧ R ⊆ T ∧ Disjoint Y R ∧ (∀ x ∈ T, x ∈ Y ∨ x ∈ R) ∧
      bsum a Y Y ≤ (S.card : ℝ) ^ 2 / 2 - bsum a S S ∧
      (R.Nonempty → ∃ v ∈ Y, ∀ y ∈ R, 0 < a v y) := by
    intro T hTS
    rcases T.eq_empty_or_nonempty with rfl | hT
    · refine ⟨∅, ∅, subset_rfl, subset_rfl, disjoint_empty_left _, by simp, ?_, by simp⟩
      have := value_bound H
      have h0 : bsum a (∅ : Finset α) ∅ = 0 := by simp [bsum]
      rw [h0]; linarith
    · obtain ⟨v, hvT, hb⟩ := greedy_step H hTS hT
      refine ⟨T.filter fun y => ¬ 0 < a v y, T.filter fun y => 0 < a v y, filter_subset _ _,
        filter_subset _ _, ?_, ?_, hb, ?_⟩
      · rw [disjoint_filter]; intro x _ h1 h2; exact h1 h2
      · intro x hx; by_cases h : 0 < a v x
        · exact Or.inr (mem_filter.2 ⟨hx, h⟩)
        · exact Or.inl (mem_filter.2 ⟨hx, h⟩)
      · intro _
        exact ⟨v, mem_filter.2 ⟨hvT, by rw [H.diag]; exact lt_irrefl 0⟩,
          fun y hy => (mem_filter.1 hy).2⟩
  obtain ⟨Y1, R1, hY1, hR1, hd1, hc1, hb1, hp1⟩ := step S subset_rfl
  obtain ⟨Y2, R2, hY2, hR2, hd2, hc2, hb2, hp2⟩ := step R1 hR1
  obtain ⟨Y3, R3, hY3, hR3, hd3, hc3, hb3, hp3⟩ := step R2 (hR2.trans hR1)
  obtain ⟨Y4, R4, hY4, hR4, hd4, hc4, hb4, hp4⟩ := step R3 (hR3.trans (hR2.trans hR1))
  -- nothing is left after four steps
  have hR4e : R4 = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := nonempty_iff_ne_empty.2 hne
    obtain ⟨v4, hv4, h4⟩ := hp4 ⟨y, hy⟩
    obtain ⟨v3, hv3, h3⟩ := hp3 ⟨v4, hY4 hv4⟩
    obtain ⟨v2, hv2, h2⟩ := hp2 ⟨v3, hY3 hv3⟩
    obtain ⟨v1, hv1, h1⟩ := hp1 ⟨v2, hY2 hv2⟩
    -- all needed positivities
    have p12 : 0 < a v1 v2 := h1 _ (hY2 hv2)
    have p13 : 0 < a v1 v3 := h1 _ (hR2 (hY3 hv3))
    have p14 : 0 < a v1 v4 := h1 _ (hR2 (hR3 (hY4 hv4)))
    have p15 : 0 < a v1 y := h1 _ (hR2 (hR3 (hR4 hy)))
    have p23 : 0 < a v2 v3 := h2 _ (hY3 hv3)
    have p24 : 0 < a v2 v4 := h2 _ (hR3 (hY4 hv4))
    have p25 : 0 < a v2 y := h2 _ (hR3 (hR4 hy))
    have p34 : 0 < a v3 v4 := h3 _ (hY4 hv4)
    have p35 : 0 < a v3 y := h3 _ (hR4 hy)
    have p45 : 0 < a v4 y := h4 _ hy
    have ne : ∀ {p q : α}, 0 < a p q → p ≠ q := fun h e => by
      rw [e, H.diag] at h; exact lt_irrefl 0 h
    set K : Finset α := {v1, v2, v3, v4, y}
    have hK : K.card = 5 := by
      simp only [K]
      rw [card_insert_of_notMem, card_insert_of_notMem, card_insert_of_notMem,
        card_pair (ne p45)]
      · simp only [mem_insert, mem_singleton, not_or]; exact ⟨ne p34, ne p35⟩
      · simp only [mem_insert, mem_singleton, not_or]; exact ⟨ne p23, ne p24, ne p25⟩
      · simp only [mem_insert, mem_singleton, not_or]; exact ⟨ne p12, ne p13, ne p14, ne p15⟩
    have hKS : K ⊆ S := by
      intro z hz
      simp only [K, mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl | rfl | rfl | rfl
      · exact hY1 hv1
      · exact hR1 (hY2 hv2)
      · exact hR1 (hR2 (hY3 hv3))
      · exact hR1 (hR2 (hR3 (hY4 hv4)))
      · exact hR1 (hR2 (hR3 (hR4 hy)))
    have hpos : ∀ i ∈ K, ∀ j ∈ K, i ≠ j → 0 < a i j := by
      have sym : ∀ {p q : α}, 0 < a p q → 0 < a q p := fun h => by rwa [H.symm]
      intro i hi j hj hij
      simp only [K, mem_insert, mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl | rfl <;>
        first | exact absurd rfl hij | assumption | exact sym ‹_›
    have := H.clique K hKS hpos
    omega
  refine ⟨![Y1, Y2, Y3, Y4], ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i
    · exact hY1
    · exact hY2.trans hR1
    · exact hY3.trans (hR2.trans hR1)
    · exact hY4.trans (hR3.trans (hR2.trans hR1))
  · -- disjointness: `Yᵢ` is disjoint from `Rᵢ`, which contains all later classes
    have d12 : Disjoint Y1 Y2 := hd1.mono_right hY2
    have d13 : Disjoint Y1 Y3 := hd1.mono_right (hY3.trans hR2)
    have d14 : Disjoint Y1 Y4 := hd1.mono_right (hY4.trans (hR3.trans hR2))
    have d23 : Disjoint Y2 Y3 := hd2.mono_right hY3
    have d24 : Disjoint Y2 Y4 := hd2.mono_right (hY4.trans hR3)
    have d34 : Disjoint Y3 Y4 := hd3.mono_right hY4
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | assumption | exact Disjoint.symm ‹_›
  · intro x hx
    rcases hc1 x hx with h | h
    · exact ⟨0, h⟩
    rcases hc2 x h with h | h
    · exact ⟨1, h⟩
    rcases hc3 x h with h | h
    · exact ⟨2, h⟩
    rcases hc4 x h with h | h
    · exact ⟨3, h⟩
    · rw [hR4e] at h; exact absurd h (notMem_empty x)
  · intro i; fin_cases i
    · exact hb1
    · exact hb2
    · exact hb3
    · exact hb4

end NashWilliams.Frac
