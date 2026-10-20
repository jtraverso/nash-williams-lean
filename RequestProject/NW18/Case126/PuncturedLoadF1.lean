/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.PuncturedWeightsF1

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: loads of the normalised punctured weighting in the actual level

`punctured_weighting` (proved) is the graph-counting adapter announced in
`PuncturedWeightsF1.lean`: on the ACTUAL damaged level `H`, with near-quarter classes of `U` and
`W \ U` (defect `κ`), typicality `ξ` of the host `G`, damage `ζ`, and a cross reserve `Res` whose
removal is `ε`-regular with surviving density `q ∈ [1/2, 1]`, the normalised weighting
`puncPhi W U q` is a `[0, 8/|W|]`-bounded weighting of the `F₁`-copies of the punctured level whose
load on EVERY punctured edge is within `32 (κ + 2ξ + 2ζ + ε)` of `1`.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-- Combination of two count errors against an exact identity. -/
lemma err_combine (a0 a1 A B x y X : ℝ) (h0 : 0 ≤ a0) (h01 : a0 ≤ a1) (hA : |A - x| ≤ X)
    (hB : |B - y| ≤ X) (hid : a0 * x + a1 * y = 1) : |a0 * A + a1 * B - 1| ≤ 2 * a1 * X := by
  have hX : 0 ≤ X := (abs_nonneg _).trans hA
  have h1 : 0 ≤ a1 := h0.trans h01
  have e : a0 * A + a1 * B - 1 = a0 * (A - x) + a1 * (B - y) := by rw [← hid]; ring
  rw [e]
  calc |a0 * (A - x) + a1 * (B - y)| ≤ |a0 * (A - x)| + |a1 * (B - y)| := abs_add_le _ _
    _ = a0 * |A - x| + a1 * |B - y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
    _ ≤ a0 * X + a1 * X :=
        add_le_add (mul_le_mul_of_nonneg_left hA h0) (mul_le_mul_of_nonneg_left hB h1)
    _ ≤ 2 * a1 * X := by nlinarith

variable {V : Type} [Fintype V] [DecidableEq V]

/-- `t = (|W| - |U|)/4`, the ideal outside class size. -/
noncomputable def tOf (W U : Finset V) : ℝ := ((W.card : ℝ) - U.card) / 4

/-- `u = |U|/4`, the ideal child class size. -/
noncomputable def uOf (U : Finset V) : ℝ := (U.card : ℝ) / 4

/-- The normalised punctured weighting with surviving reserve density `q`. -/
noncomputable def puncPhi (W U : Finset V) (q : ℝ) : Finset V → ℝ :=
  puncWeight U (w0 (tOf W U) (uOf U) q) (w1 (tOf W U) q)

omit [Fintype V] [DecidableEq V] in
lemma punc_adj (H : SimpleGraph V) (W U : Finset V) (Res : Finset (Sym2 V)) (a b : V) :
    (punc H W U Res).Adj a b ↔
      H.Adj a b ∧ a ∈ W ∧ b ∈ W ∧ ¬ (a ∈ U ∧ b ∈ U) ∧ s(a, b) ∉ Res := Iff.rfl

section Load

variable (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V)
  (Res : Finset (Sym2 V))

/-- The admissible third vertices of a punctured edge `ab`. -/
def thirdSet (a b : V) : Finset V :=
  univ.filter fun z => (punc H W U Res).Adj a z ∧ (punc H W U Res).Adj z b ∧
    ({p a, p b, p z} : Multiset (Fin 4)) ∈ F1

/-- An allowed pair has exactly two third classes. -/
lemma thirds_pair (i j : Fin 4) (h : AllowedT F1 i j) :
    ∃ l₁ l₂ : Fin 4, l₁ ≠ l₂ ∧ thirdsT F1 i j = {l₁, l₂} :=
  card_eq_two.mp (twoThirds_F1' i j h)

omit [Fintype V] [DecidableEq V] in
/-- Splitting a set of third vertices along the two third classes. -/
lemma card_split_thirds (a b : V) (S : Finset V) (l₁ l₂ : Fin 4) (hl : l₁ ≠ l₂)
    (hT : thirdsT F1 (p a) (p b) = {l₁, l₂})
    (hS : ∀ z ∈ S, ({p a, p b, p z} : Multiset (Fin 4)) ∈ F1) :
    S.card = (S.filter fun z => p z = l₁).card + (S.filter fun z => p z = l₂).card := by
  rw [card_eq_sum_card_fiberwise (f := p) (t := thirdsT F1 (p a) (p b))]
  · rw [hT, sum_pair hl]
  · intro z hz
    rw [mem_coe, thirdsT, mem_filter]
    exact ⟨mem_univ _, hS z hz⟩

variable {p H W U Res}

/-- Outside third vertices of an outside-outside edge. -/
lemma thirdSet_out_out {a b : V} (ha : a ∈ W) (hb : b ∈ W) (haU : a ∉ U) (hbU : b ∉ U)
    (hR0 : ∀ x z, x ∉ U → z ∉ U → s(x, z) ∉ Res) {l : Fin 4}
    (hl : l ∈ thirdsT F1 (p a) (p b)) :
    ((thirdSet p H W U Res a b).filter fun z => z ∉ U).filter (fun z => p z = l) =
      (W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z := by
  ext z
  simp only [thirdSet, mem_filter, mem_univ, true_and, mem_sdiff, punc_adj]
  constructor
  · rintro ⟨⟨⟨⟨hHaz, -, hzW, -, -⟩, ⟨hHzb, -, -, -, -⟩, -⟩, hzU⟩, hzl⟩
    exact ⟨⟨hzW, hzU⟩, hzl, hHaz, hHzb.symm⟩
  · rintro ⟨⟨hzW, hzU⟩, hzl, hHaz, hHbz⟩
    refine ⟨⟨⟨⟨hHaz, ha, hzW, fun h => haU h.1, hR0 a z haU hzU⟩,
      ⟨hHbz.symm, hzW, hb, fun h => hzU h.1, hR0 z b hzU hbU⟩, ?_⟩, hzU⟩, hzl⟩
    rw [hzl]; exact (mem_filter.mp hl).2

/-- Child third vertices of an outside-outside edge. -/
lemma thirdSet_out_in {a b : V} (ha : a ∈ W) (hb : b ∈ W) (haU : a ∉ U) (hbU : b ∉ U)
    (hUW : U ⊆ W) {l : Fin 4} (hl : l ∈ thirdsT F1 (p a) (p b)) :
    ((thirdSet p H W U Res a b).filter fun z => z ∈ U).filter (fun z => p z = l) =
      U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∉ Res ∧ s(b, z) ∉ Res := by
  ext z
  simp only [thirdSet, mem_filter, mem_univ, true_and, punc_adj]
  constructor
  · rintro ⟨⟨⟨⟨hHaz, -, -, -, hRa⟩, ⟨hHzb, -, -, -, hRb⟩, -⟩, hzU⟩, hzl⟩
    exact ⟨hzU, hzl, hHaz, hHzb.symm, hRa, by rw [Sym2.eq_swap]; exact hRb⟩
  · rintro ⟨hzU, hzl, hHaz, hHbz, hRa, hRb⟩
    refine ⟨⟨⟨⟨hHaz, ha, hUW hzU, fun h => haU h.1, hRa⟩,
      ⟨hHbz.symm, hUW hzU, hb, fun h => hbU h.2, by rw [Sym2.eq_swap]; exact hRb⟩, ?_⟩, hzU⟩,
      hzl⟩
    rw [hzl]; exact (mem_filter.mp hl).2

/-- Third vertices of an outside-child edge (all outside). -/
lemma thirdSet_out_child {a b : V} (ha : a ∈ W) (hbU : b ∈ U) (haU : a ∉ U) (hUW : U ⊆ W)
    (hR0 : ∀ x z, x ∉ U → z ∉ U → s(x, z) ∉ Res) {l : Fin 4}
    (hl : l ∈ thirdsT F1 (p a) (p b)) :
    (thirdSet p H W U Res a b).filter (fun z => p z = l) =
      (W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(b, z) ∉ Res := by
  ext z
  simp only [thirdSet, mem_filter, mem_univ, true_and, mem_sdiff, punc_adj]
  constructor
  · rintro ⟨⟨⟨hHaz, -, hzW, -, -⟩, ⟨hHzb, -, -, hzb, hRb⟩, -⟩, hzl⟩
    have hzU : z ∉ U := fun h => hzb ⟨h, hbU⟩
    exact ⟨⟨hzW, hzU⟩, hzl, hHaz, hHzb.symm, by rw [Sym2.eq_swap]; exact hRb⟩
  · rintro ⟨⟨hzW, hzU⟩, hzl, hHaz, hHbz, hRb⟩
    refine ⟨⟨⟨hHaz, ha, hzW, fun h => haU h.1, hR0 a z haU hzU⟩,
      ⟨hHbz.symm, hzW, hUW hbU, fun h => hzU h.1, by rw [Sym2.eq_swap]; exact hRb⟩, ?_⟩, hzl⟩
    rw [hzl]; exact (mem_filter.mp hl).2

end Load

/-- Deviation of a reserve-thinned common-neighbourhood count from its ideal value. -/
lemma scaled_dev (q C D O t n κ ξ ζ ε : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hD : |D - q * C| ≤ ε * n)
    (hC1 : O - 2 * ξ * n - 2 * ζ * n ≤ C) (hC2 : C ≤ O) (hO : |O - t| ≤ κ * n) :
    |D - q * t| ≤ (κ + 2 * ξ + 2 * ζ + ε) * n := by
  have hO' := abs_le.mp hO
  have hCt : |C - t| ≤ (κ + 2 * ξ + 2 * ζ) * n := by
    rw [abs_le]; constructor <;> nlinarith
  have hqC : |q * C - q * t| ≤ (κ + 2 * ξ + 2 * ζ) * n := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hq0]
    have h0 : 0 ≤ |C - t| := abs_nonneg _
    nlinarith
  calc |D - q * t| = |(D - q * C) + (q * C - q * t)| := by ring_nf
    _ ≤ |D - q * C| + |q * C - q * t| := abs_add_le _ _
    _ ≤ ε * n + (κ + 2 * ξ + 2 * ζ) * n := add_le_add hD hqC
    _ = (κ + 2 * ξ + 2 * ζ + ε) * n := by ring

/-- Two class errors add up. -/
lemma two_dev (D₁ D₂ x X : ℝ) (h₁ : |D₁ - x| ≤ X) (h₂ : |D₂ - x| ≤ X) :
    |D₁ + D₂ - 2 * x| ≤ 2 * X := by
  have e : D₁ + D₂ - 2 * x = (D₁ - x) + (D₂ - x) := by ring
  rw [e]; linarith [abs_add_le (D₁ - x) (D₂ - x)]

section Main

variable (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
  (W U : Finset V) (Res : Finset (Sym2 V)) (κ ξ ζ ε q : ℝ)

/-- The hypotheses of the punctured weighting, bundled. -/
structure PuncHyp : Prop where
  hUW : U ⊆ W
  hW : 0 < W.card
  hUh : (U.card : ℝ) ≤ W.card / 2
  hq : 1 / 2 ≤ q
  hq1 : q ≤ 1
  hκ : 0 ≤ κ
  hξ : 0 ≤ ξ
  hζ : 0 ≤ ζ
  hε : 0 ≤ ε
  hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)
  hHG : H ≤ G
  hout : ∀ j : Fin 4, |(((W \ U).filter fun z => p z = j).card : ℝ) - tOf W U| ≤ κ * W.card
  hin : ∀ j : Fin 4, |((U.filter fun z => p z = j).card : ℝ) - uOf U| ≤ κ * W.card
  htyp : ∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
    ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card
  hdam : ∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card
  hR0 : ∀ x z, x ∉ U → z ∉ U → s(x, z) ∉ Res
  hR1 : ∀ a ∈ W, ∀ b ∈ W, a ≠ b → a ∉ U → b ∉ U → ∀ l : Fin 4,
    |((U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∉ Res ∧ s(b, z) ∉ Res).card
        : ℝ) - q ^ 2 * (U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| ≤ ε * W.card
  hR2 : ∀ a ∈ W, ∀ b ∈ U, a ∉ U → ∀ l : Fin 4,
    |(((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(b, z) ∉ Res).card : ℝ) -
        q * ((W \ U).filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card| ≤ ε * W.card

variable {p G H W U Res κ ξ ζ ε q}

omit [Fintype V] in
lemma PuncHyp.scalars (h : PuncHyp p G H W U Res κ ξ ζ ε q) :
    0 < tOf W U ∧ (W.card : ℝ) / 8 ≤ tOf W U ∧ 0 ≤ uOf U ∧ uOf U * q ≤ tOf W U ∧ 0 < q ∧
      0 ≤ w0 (tOf W U) (uOf U) q ∧ w0 (tOf W U) (uOf U) q ≤ w1 (tOf W U) q ∧
      w1 (tOf W U) q ≤ 8 / W.card := by
  have hn : (0 : ℝ) < W.card := by exact_mod_cast h.hW
  have hU0 : (0 : ℝ) ≤ U.card := Nat.cast_nonneg _
  have ht8 : (W.card : ℝ) / 8 ≤ tOf W U := by unfold tOf; linarith [h.hUh]
  have ht : 0 < tOf W U := lt_of_lt_of_le (by positivity) ht8
  have hu : 0 ≤ uOf U := by unfold uOf; positivity
  have hq0 : 0 < q := by linarith [h.hq]
  have huq : uOf U * q ≤ tOf W U := by
    have : uOf U ≤ tOf W U := by unfold uOf tOf; linarith [h.hUh]
    nlinarith [h.hq1]
  refine ⟨ht, ht8, hu, huq, hq0, w0_nonneg _ _ _ ht huq, w0_le_w1 _ _ _ ht hq0 h.hq1 hu, ?_⟩
  unfold w1
  rw [div_le_div_iff₀ (by positivity) hn]
  nlinarith [h.hq]

/-- **Load of the normalised punctured weighting at an edge with an outside endpoint.** -/
theorem punctured_load_at (h : PuncHyp p G H W U Res κ ξ ζ ε q) {a b : V}
    (hab : (punc H W U Res).Adj a b) (haU : a ∉ U) :
    |(∑ s ∈ (copies p F1 (punc H W U Res)).filter (fun s => s(a, b) ∈ triEdges s),
        puncPhi W U q s) - 1| ≤ 32 * (κ + 2 * ξ + 2 * ζ + ε) := by
  obtain ⟨ht, ht8, hu, huq, hq0, hw0, hw01, hw1⟩ := h.scalars
  have hn : (0 : ℝ) < W.card := by exact_mod_cast h.hW
  set n : ℝ := (W.card : ℝ) with hndef
  set E : ℝ := κ + 2 * ξ + 2 * ζ + ε with hE
  have hE0 : 0 ≤ E := by have := h.hκ; have := h.hξ; have := h.hζ; have := h.hε; positivity
  have hab' := hab
  obtain ⟨hHab, ha, hb, -, -⟩ := hab
  have hall : AllowedT F1 (p a) (p b) := h.hGF a b (h.hHG hHab)
  obtain ⟨l₁, l₂, hl, hT⟩ := thirds_pair (p a) (p b) hall
  have hl₁ : l₁ ∈ thirdsT F1 (p a) (p b) := by rw [hT]; simp
  have hl₂ : l₂ ∈ thirdsT F1 (p a) (p b) := by rw [hT]; simp
  have hallow : ∀ l ∈ thirdsT F1 (p a) (p b), AllowedT F1 (p a) l ∧ AllowedT F1 (p b) l :=
    fun l hl => ⟨allowedT_of_mem (mem_filter.mp hl).2, allowedT_of_mem' (mem_filter.mp hl).2⟩
  rw [sum_copies_through p F1 (punc H W U Res) hab' (puncPhi W U q)]
  change |∑ z ∈ thirdSet p H W U Res a b, puncPhi W U q {a, b, z} - 1| ≤ 32 * E
  set Z := thirdSet p H W U Res a b with hZ
  have hZF : ∀ z ∈ Z, ({p a, p b, p z} : Multiset (Fin 4)) ∈ F1 :=
    fun z hz => (mem_filter.mp hz).2.2.2
  by_cases hbU : b ∈ U
  · -- outside-child edge
    have hval : ∀ z ∈ Z, puncPhi W U q {a, b, z} = w1 (tOf W U) q := by
      intro z _
      unfold puncPhi puncWeight
      rw [if_neg]
      rw [disjoint_left]; push_neg
      exact ⟨b, by simp, hbU⟩
    rw [sum_congr rfl hval, sum_const, nsmul_eq_mul]
    have hsplit := card_split_thirds p a b Z l₁ l₂ hl hT hZF
    have hD : ∀ l ∈ thirdsT F1 (p a) (p b),
        |((Z.filter fun z => p z = l).card : ℝ) - q * tOf W U| ≤ E * n := by
      intro l hlT
      rw [hZ, thirdSet_out_child ha hbU haU h.hUW h.hR0 hlT]
      obtain ⟨hC1, hC2⟩ := common_count_bounds p G H W (W \ U) sdiff_subset ξ ζ h.htyp h.hdam
        a b ha hb l (hallow l hlT).1 (hallow l hlT).2
      exact scaled_dev q _ _ _ _ n κ ξ ζ ε hq0.le h.hq1
        (h.hR2 a ha b hbU haU l) hC1 hC2 (h.hout l)
    have h2 := two_dev _ _ _ _ (hD l₁ hl₁) (hD l₂ hl₂)
    have hcast : ((Z.card : ℕ) : ℝ) = ((Z.filter fun z => p z = l₁).card : ℝ) +
        (Z.filter fun z => p z = l₂).card := by exact_mod_cast hsplit
    rw [hcast]
    have hid := w_boundary_load (tOf W U) q ht hq0
    have e : (((Z.filter fun z => p z = l₁).card : ℝ) + (Z.filter fun z => p z = l₂).card) *
        w1 (tOf W U) q - 1 = w1 (tOf W U) q * (((Z.filter fun z => p z = l₁).card : ℝ) +
          (Z.filter fun z => p z = l₂).card - 2 * (q * tOf W U)) := by
      rw [← hid]; ring
    rw [e, abs_mul, abs_of_nonneg (hw0.trans hw01)]
    calc w1 (tOf W U) q * |((Z.filter fun z => p z = l₁).card : ℝ) +
          (Z.filter fun z => p z = l₂).card - 2 * (q * tOf W U)|
        ≤ (8 / n) * (2 * (E * n)) :=
          mul_le_mul hw1 h2 (abs_nonneg _) (by positivity)
      _ = 16 * E := by field_simp; ring
      _ ≤ 32 * E := by linarith
  · -- outside-outside edge
    have hin_val : ∀ z ∈ Z.filter (fun z => z ∈ U), puncPhi W U q {a, b, z} =
        w1 (tOf W U) q := by
      intro z hz
      unfold puncPhi puncWeight
      rw [if_neg]
      rw [disjoint_left]; push_neg
      exact ⟨z, by simp, (mem_filter.mp hz).2⟩
    have hout_val : ∀ z ∈ Z.filter (fun z => z ∉ U), puncPhi W U q {a, b, z} =
        w0 (tOf W U) (uOf U) q := by
      intro z hz
      unfold puncPhi puncWeight
      rw [if_pos]
      rw [disjoint_left]
      intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact haU
      · exact hbU
      · exact (mem_filter.mp hz).2
    rw [← sum_filter_add_sum_filter_not Z (fun z => z ∈ U), sum_congr rfl hin_val,
      sum_congr rfl hout_val, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul]
    have hsIn := card_split_thirds p a b (Z.filter fun z => z ∈ U) l₁ l₂ hl hT
      (fun z hz => hZF z (mem_filter.mp hz).1)
    have hsOut := card_split_thirds p a b (Z.filter fun z => z ∉ U) l₁ l₂ hl hT
      (fun z hz => hZF z (mem_filter.mp hz).1)
    have hB : ∀ l ∈ thirdsT F1 (p a) (p b),
        |(((Z.filter fun z => z ∈ U).filter fun z => p z = l).card : ℝ) - q ^ 2 * uOf U|
          ≤ E * n := by
      intro l hlT
      rw [hZ, thirdSet_out_in ha hb haU hbU h.hUW hlT]
      obtain ⟨hC1, hC2⟩ := common_count_bounds p G H W U h.hUW ξ ζ h.htyp h.hdam
        a b ha hb l (hallow l hlT).1 (hallow l hlT).2
      exact scaled_dev (q ^ 2) _ _ _ _ n κ ξ ζ ε (by positivity)
        (by nlinarith [h.hq1])
        (h.hR1 a ha b hb (H.ne_of_adj hHab) haU hbU l) hC1 hC2 (h.hin l)
    have hA : ∀ l ∈ thirdsT F1 (p a) (p b),
        |(((Z.filter fun z => z ∉ U).filter fun z => p z = l).card : ℝ) - 1 * tOf W U|
          ≤ E * n := by
      intro l hlT
      rw [hZ, thirdSet_out_out ha hb haU hbU h.hR0 hlT]
      obtain ⟨hC1, hC2⟩ := common_count_bounds p G H W (W \ U) sdiff_subset ξ ζ h.htyp h.hdam
        a b ha hb l (hallow l hlT).1 (hallow l hlT).2
      refine scaled_dev 1 _ _ _ _ n κ ξ ζ ε zero_le_one le_rfl ?_ hC1 hC2
        (h.hout l)
      rw [one_mul, sub_self, abs_zero]; exact mul_nonneg h.hε hn.le
    have hB2 := two_dev _ _ _ _ (hB l₁ hl₁) (hB l₂ hl₂)
    have hA2 := two_dev _ _ _ _ (hA l₁ hl₁) (hA l₂ hl₂)
    have hcIn : (((Z.filter fun z => z ∈ U).card : ℕ) : ℝ) =
        (((Z.filter fun z => z ∈ U).filter fun z => p z = l₁).card : ℝ) +
        ((Z.filter fun z => z ∈ U).filter fun z => p z = l₂).card := by exact_mod_cast hsIn
    have hcOut : (((Z.filter fun z => z ∉ U).card : ℕ) : ℝ) =
        (((Z.filter fun z => z ∉ U).filter fun z => p z = l₁).card : ℝ) +
        ((Z.filter fun z => z ∉ U).filter fun z => p z = l₂).card := by exact_mod_cast hsOut
    rw [hcIn, hcOut]
    have hid : w0 (tOf W U) (uOf U) q * (2 * (1 * tOf W U)) +
        w1 (tOf W U) q * (2 * (q ^ 2 * uOf U)) = 1 := by
      have := w_outside_load (tOf W U) (uOf U) q ht
      linarith
    have hc := err_combine _ _ _ _ _ _ _ hw0 hw01 hA2 hB2 hid
    have e : (((Z.filter fun z => z ∈ U).filter fun z => p z = l₁).card +
        ((Z.filter fun z => z ∈ U).filter fun z => p z = l₂).card : ℝ) * w1 (tOf W U) q +
        (((Z.filter fun z => z ∉ U).filter fun z => p z = l₁).card +
        ((Z.filter fun z => z ∉ U).filter fun z => p z = l₂).card : ℝ) *
          w0 (tOf W U) (uOf U) q =
        w0 (tOf W U) (uOf U) q * ((((Z.filter fun z => z ∉ U).filter fun z => p z = l₁).card +
        ((Z.filter fun z => z ∉ U).filter fun z => p z = l₂).card : ℝ)) +
        w1 (tOf W U) q * ((((Z.filter fun z => z ∈ U).filter fun z => p z = l₁).card +
        ((Z.filter fun z => z ∈ U).filter fun z => p z = l₂).card : ℝ)) := by ring
    rw [e]
    calc _ ≤ 2 * w1 (tOf W U) q * (2 * (E * n)) := hc
      _ ≤ 2 * (8 / n) * (2 * (E * n)) := by
          have : 0 ≤ 2 * (E * n) := by positivity
          nlinarith
      _ = 32 * E := by field_simp; ring

/-- **The normalised punctured weighting of the actual level (producer, proved).**  Every copy
weight is in `[0, 8/|W|]`, and the load of EVERY edge of the punctured level is within
`32 (κ + 2ξ + 2ζ + ε)` of `1`. -/
theorem punctured_weighting (h : PuncHyp p G H W U Res κ ξ ζ ε q) :
    (∀ s, 0 ≤ puncPhi W U q s ∧ puncPhi W U q s ≤ 8 / W.card) ∧
    ∀ e ∈ (punc H W U Res).edgeFinset,
      |(∑ s ∈ copies p F1 (punc H W U Res) with e ∈ triEdges s, puncPhi W U q s) - 1| ≤
        32 * (κ + 2 * ξ + 2 * ζ + ε) := by
  obtain ⟨-, -, -, -, -, hw0, hw01, hw1⟩ := h.scalars
  refine ⟨fun s => ?_, fun e he => ?_⟩
  · unfold puncPhi puncWeight
    split_ifs
    · exact ⟨hw0, hw01.trans hw1⟩
    · exact ⟨hw0.trans hw01, hw1⟩
  · induction e using Sym2.ind with
    | _ a b =>
    have hab : (punc H W U Res).Adj a b := SimpleGraph.mem_edgeFinset.mp he
    by_cases haU : a ∈ U
    · have hbU : b ∉ U := fun hb => hab.2.2.2.1 ⟨haU, hb⟩
      rw [Sym2.eq_swap]
      exact punctured_load_at h hab.symm hbU
    · exact punctured_load_at h hab haU

/-- The class missed by each class in `F₁`. -/
def missedF1 : Fin 4 → Fin 4 := ![1, 0, 3, 2]

lemma not_allowedT_missedF1 : ∀ i : Fin 4, ¬ AllowedT F1 i (missedF1 i) := by decide

/-- **Degree gap of the punctured level** (input of the near-load nibble): every vertex has
punctured degree at most `(1 - (1/8 - κ)) |W|`, since it misses the whole outside part of the
class missed by its class. -/
theorem punc_degree_le (h : PuncHyp p G H W U Res κ ξ ζ ε q) (v : V) :
    (((punc H W U Res).edgeFinset.filter fun e => v ∈ e).card : ℝ) ≤
      (1 - (1 / 8 - κ)) * W.card := by
  obtain ⟨-, ht8, -⟩ := h.scalars
  rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
  set M := (W \ U).filter fun z => p z = missedF1 (p v) with hM
  have hsub : (punc H W U Res).neighborFinset v ⊆ W \ M := by
    intro z hz
    rw [SimpleGraph.mem_neighborFinset] at hz
    rw [mem_sdiff]
    refine ⟨hz.2.2.1, fun hzM => ?_⟩
    have hzl : p z = missedF1 (p v) := (mem_filter.mp hzM).2
    have := h.hGF v z (h.hHG hz.1)
    rw [hzl] at this
    exact not_allowedT_missedF1 _ this
  have hMW : M ⊆ W := fun z hz => (mem_sdiff.mp (mem_filter.mp hz).1).1
  have hc := card_le_card hsub
  rw [card_sdiff_of_subset hMW, SimpleGraph.card_neighborFinset_eq_degree] at hc
  have hMc := abs_le.mp (h.hout (missedF1 (p v)))
  have hMle : M.card ≤ W.card := card_le_card hMW
  have hc' : ((punc H W U Res).degree v : ℝ) ≤ (W.card : ℝ) - M.card := by
    rw [← Nat.cast_sub hMle]; exact_mod_cast hc
  rw [← hM] at hMc
  nlinarith [hMc.1]

end Main

end NashWilliams18.SpreadF1
