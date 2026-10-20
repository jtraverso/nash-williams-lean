/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.BalancedWeightingF1
import PartitionedTriangleAbsorption.F1PaddedWeightsStage233

/-!
# Exact positive weights on the actual punctured `F₁` level (small child, zero balance)

This is the application of the physical incidence inverse
(`F1TemplateStage233.f1_padded_exact_weights`) to the actual punctured graph
`punc H W U Res` on the ACTIVE vertex set `W`.

* `F1_punctured_exact_weights`: with near-quarter classes of `W` (defect `κ`), typicality `ξ` of
  the allowed host `G`, damage `ζ`, a SMALL child `|U| ≤ β |W|`, reserve degree `≤ ρ |W|`,
  the numerical condition `3ξ + ζ + β + ρ + 6κ ≤ 1/5120`, `|W| ≥ 20480`, and EXACT zero balance of
  the punctured graph, the actual F1 triangles of `punc H W U Res` carry weights in
  `[1/(2|W|), 3/|W|]` with load exactly one on every punctured edge.  The deleted child edges
  (`β`), reserve degree (`ρ`), inherited damage (`ξ`, `ζ`) and padding (`6κ`) are all counted in
  the single bound `D + 3s ≤ t/640`.
* `F1_punchyp_exact_weights`: the same on the `PuncHyp` domain, restricted to a small child ratio
  and a reserve-degree bound; near-quarter classes of `W` are derived from those of `U`, `W \ U`.

The zero-balance premise is NOT derived here: it is the output of the reserve repair (Stage 231,
`exists_balanced_reserve_extension`), which must be applied to the actual graph and sample.
This file does NOT prove the broader `F1BalancedRobustWeighting` (whose domain allows
`|U| ≤ |W|/2`).
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1 first1 second1)
open PartitionedTriangleAbsorption.F1BalanceGateStage228 (charge balance)
open PartitionedTriangleAbsorption.F1TemplateStage233 (Opp opp_cases f1_padded_exact_weights)

theorem allowedT_F1_iff (i j : Fin 4) : AllowedT F1 i j ↔ (i = j ∨ Opp i j) := by
  revert i j; decide

variable {V : Type} [Fintype V] [DecidableEq V]

/-- **Exact positive weights on the actual punctured level.** -/
theorem F1_punctured_exact_weights (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W U : Finset V) (Res : Finset (Sym2 V)) {κ ξ ζ β ρ : ℝ}
    (hGF : ∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) (hHG : H ≤ G)
    (hcls : ∀ j : Fin 4, |((W.filter fun z => p z = j).card : ℝ) - W.card / 4| ≤ κ * W.card)
    (htyp : ∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card)
    (hdam : ∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card)
    (hU : (U.card : ℝ) ≤ β * W.card)
    (hRes : ∀ u ∈ W, ((W.filter fun v => s(u, v) ∈ Res).card : ℝ) ≤ ρ * W.card)
    (hsmall : 3 * ξ + ζ + β + ρ + 6 * κ ≤ 1 / 5120) (hN : 20480 ≤ W.card)
    (hbal : balance p (punc H W U Res).edgeFinset = 0) :
    ∃ w : Finset V → ℝ,
      (∀ e ∈ (punc H W U Res).edgeFinset, F1BalanceGateStage228.load (copies p F1 (punc H W U Res)) w e = 1) ∧
      (∀ x ∈ copies p F1 (punc H W U Res), 1 / (2 * W.card) ≤ w x ∧ w x ≤ 3 / W.card) ∧
      (∀ x ∉ copies p F1 (punc H W U Res), w x = 0) := by
  set n : ℝ := (W.card : ℝ) with hn
  have hn0 : (20480 : ℝ) ≤ n := by rw [hn]; exact_mod_cast hN
  have hκ : 0 ≤ κ := by
    have := (abs_nonneg _).trans (hcls 0)
    by_contra h; push_neg at h; nlinarith
  -- template size `t` and padding `s`
  set t : ℕ := ⌊n / 4 + κ * n⌋₊ with ht
  set s : ℕ := ⌈2 * κ * n⌉₊ with hs
  have hκn : 0 ≤ κ * n := by positivity
  have ht_le : (t : ℝ) ≤ n / 4 + κ * n := Nat.floor_le (by positivity)
  have ht_ge : n / 4 + κ * n - 1 < t := by
    have := Nat.lt_floor_add_one (n / 4 + κ * n); rw [← ht] at this; linarith
  have hs_le : (s : ℝ) < 2 * κ * n + 1 := Nat.ceil_lt_add_one (by positivity)
  have hs_ge : 2 * κ * n ≤ s := Nat.le_ceil _
  have ht640 : 640 ≤ t := by
    have : (640 : ℝ) < t + 1 := by linarith
    have : (639 : ℝ) < t := by linarith
    exact_mod_cast (show (639 : ℝ) < t from this)
  have hclsN : ∀ i, t ≤ (W.filter fun v => p v = i).card + s ∧
      (W.filter fun v => p v = i).card ≤ t := by
    intro i
    obtain ⟨h1, h2⟩ := abs_le.mp (hcls i)
    constructor
    · have : (t : ℝ) ≤ (W.filter fun v => p v = i).card + s := by linarith
      exact_mod_cast this
    · apply Nat.le_floor; linarith
  -- missing degree
  set D : ℝ := (3 * ξ + ζ + β + ρ) * n with hD
  have hHW : ∀ u v, (punc H W U Res).Adj u v → u ∈ W := fun u v h => h.2.1
  have hallowed : ∀ u v, (punc H W U Res).Adj u v → p u = p v ∨ Opp (p u) (p v) :=
    fun u v h => (allowedT_F1_iff _ _).mp (hGF u v (hHG h.1))
  have hdmg : ∀ u, (∃ v, (punc H W U Res).Adj u v) →
      ((W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧
        ¬ (punc H W U Res).Adj u w).card : ℝ) ≤ D := by
    rintro u ⟨v, huv⟩
    have hu : u ∈ W := huv.2.1
    have hsub : (W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧
        ¬ (punc H W U Res).Adj u w) ⊆
        ((W.filter fun z => p z = p u ∧ ¬ G.Adj u z) ∪
          ((W.filter fun z => p z = first1 (p u) ∧ ¬ G.Adj u z) ∪
            (W.filter fun z => p z = second1 (p u) ∧ ¬ G.Adj u z))) ∪
        ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v) ∪
          (U ∪ (W.filter fun v => s(u, v) ∈ Res))) := by
      intro w hw
      simp only [mem_filter] at hw
      obtain ⟨hwW, -, hcl, hnot⟩ := hw
      simp only [mem_union, mem_filter]
      by_cases hG : G.Adj u w
      · by_cases hH : H.Adj u w
        · by_cases hUU : u ∈ U ∧ w ∈ U
          · exact Or.inr (Or.inr (Or.inl hUU.2))
          · by_cases hR : s(u, w) ∈ Res
            · exact Or.inr (Or.inr (Or.inr ⟨hwW, hR⟩))
            · exact absurd ⟨hH, hu, hwW, hUU, hR⟩ hnot
        · exact Or.inr (Or.inl ⟨hwW, hG, hH⟩)
      · left
        rcases hcl with h | h
        · exact Or.inl ⟨hwW, h.symm, hG⟩
        · rcases opp_cases h with h' | h'
          · exact Or.inr (Or.inl ⟨hwW, h', hG⟩)
          · exact Or.inr (Or.inr ⟨hwW, h', hG⟩)
    have hcard := card_le_card hsub
    have c1 := card_union_le ((W.filter fun z => p z = p u ∧ ¬ G.Adj u z) ∪
          ((W.filter fun z => p z = first1 (p u) ∧ ¬ G.Adj u z) ∪
            (W.filter fun z => p z = second1 (p u) ∧ ¬ G.Adj u z)))
        ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v) ∪
          (U ∪ (W.filter fun v => s(u, v) ∈ Res)))
    have c2 := card_union_le (W.filter fun z => p z = p u ∧ ¬ G.Adj u z)
          ((W.filter fun z => p z = first1 (p u) ∧ ¬ G.Adj u z) ∪
            (W.filter fun z => p z = second1 (p u) ∧ ¬ G.Adj u z))
    have c3 := card_union_le (W.filter fun z => p z = first1 (p u) ∧ ¬ G.Adj u z)
            (W.filter fun z => p z = second1 (p u) ∧ ¬ G.Adj u z)
    have c4 := card_union_le (W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v)
          (U ∪ (W.filter fun v => s(u, v) ∈ Res))
    have c5 := card_union_le U (W.filter fun v => s(u, v) ∈ Res)
    have t1 := htyp u hu (p u) ((allowedT_F1_iff _ _).mpr (Or.inl rfl))
    have t2 := htyp u hu (first1 (p u)) ((allowedT_F1_iff _ _).mpr
      (Or.inr (PartitionedTriangleAbsorption.F1TemplateStage233.opp_first1 _)))
    have t3 := htyp u hu (second1 (p u)) ((allowedT_F1_iff _ _).mpr
      (Or.inr (PartitionedTriangleAbsorption.F1TemplateStage233.opp_second1 _)))
    have t4 := hdam u hu
    have t5 := hRes u hu
    have hreal : ((W.filter fun w => w ≠ u ∧ (p u = p w ∨ Opp (p u) (p w)) ∧
        ¬ (punc H W U Res).Adj u w).card : ℝ) ≤
        (W.filter fun z => p z = p u ∧ ¬ G.Adj u z).card +
        (W.filter fun z => p z = first1 (p u) ∧ ¬ G.Adj u z).card +
        (W.filter fun z => p z = second1 (p u) ∧ ¬ G.Adj u z).card +
        (W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card + U.card +
        (W.filter fun v => s(u, v) ∈ Res).card := by
      have h0 := hcard.trans (c1.trans (add_le_add (c2.trans (add_le_add le_rfl c3))
        (c4.trans (add_le_add le_rfl c5))))
      have h0' := (Nat.cast_le (α := ℝ)).mpr h0
      push_cast at h0'
      linarith
    rw [hD]; nlinarith
  have hDs : D + 3 * s ≤ t / 640 := by
    have : (3 * ξ + ζ + β + ρ) * n + 6 * κ * n ≤ n / 5120 := by nlinarith
    have : (t : ℝ) / 640 ≥ (n / 4 + κ * n - 1) / 640 := by
      apply div_le_div_of_nonneg_right ht_ge.le (by norm_num)
    rw [hD]; nlinarith
  exact f1_padded_exact_weights p (punc H W U Res) W ht640 hclsN hHW hallowed hDs hdmg hbal

/-- **The same on the `PuncHyp` domain, restricted to a small child ratio and a reserve-degree
bound.** Near-quarter classes of `W` (defect `2κ`) are derived from those of `U` and `W \ U`. -/
theorem F1_punchyp_exact_weights (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W U : Finset V) (Res : Finset (Sym2 V)) {κ ξ ζ ε q β ρ : ℝ}
    (h : PuncHyp p G H W U Res κ ξ ζ ε q)
    (hU : (U.card : ℝ) ≤ β * W.card)
    (hRes : ∀ u ∈ W, ((W.filter fun v => s(u, v) ∈ Res).card : ℝ) ≤ ρ * W.card)
    (hsmall : 3 * ξ + ζ + β + ρ + 12 * κ ≤ 1 / 5120) (hN : 20480 ≤ W.card)
    (hbal : balance p (punc H W U Res).edgeFinset = 0) :
    ∃ w : Finset V → ℝ,
      (∀ e ∈ (punc H W U Res).edgeFinset, F1BalanceGateStage228.load (copies p F1 (punc H W U Res)) w e = 1) ∧
      (∀ x ∈ copies p F1 (punc H W U Res), 1 / (2 * W.card) ≤ w x ∧ w x ≤ 3 / W.card) ∧
      (∀ x ∉ copies p F1 (punc H W U Res), w x = 0) := by
  have hcls : ∀ j : Fin 4,
      |((W.filter fun z => p z = j).card : ℝ) - W.card / 4| ≤ (2 * κ) * W.card := by
    intro j
    have hsplit : (W.filter fun z => p z = j).card =
        ((W \ U).filter fun z => p z = j).card + (U.filter fun z => p z = j).card := by
      rw [← card_union_of_disjoint (disjoint_filter_filter sdiff_disjoint), ← filter_union,
        sdiff_union_of_subset h.hUW]
    have h1 := h.hout j
    have h2 := h.hin j
    rw [hsplit]; push_cast
    have e : (W.card : ℝ) / 4 = tOf W U + uOf U := by unfold tOf uOf; ring
    rw [e]
    calc _ = |(((W \ U).filter fun z => p z = j).card - tOf W U) +
          ((U.filter fun z => p z = j).card - uOf U)| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ κ * W.card + κ * W.card := add_le_add h1 h2
      _ = 2 * κ * W.card := by ring
  exact F1_punctured_exact_weights p G H W U Res h.hGF h.hHG hcls h.htyp h.hdam hU hRes
    (by linarith) hN hbal

end NashWilliams18.SpreadF1
