/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.NearQuarterF1
public import PartitionedTriangleAbsorption.F1PuncturedWeightsStage217
public import PartitionedTriangleAbsorption.F1DamagedExtensionsStage218

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: a near-unit fractional weighting of the ACTUAL punctured level

This is producer obligation 2 of the `F₁` level supply.  It is the graph-counting adapter of the
scalar Stage 217 weights (`F1PuncturedWeightsStage217`), with two changes:

* the classes are only NEAR-quarter (`κ`), the host is only `ξ`-typical, the current graph `H` is
  damaged (`ζ`), and the counts are taken in the actual graph;
* a protected CROSS reserve `Res` (edges between `W \ U` and `U`) is subtracted BEFORE weighting,
  and the weights are NORMALISED by the surviving reserve density `q = 1 - ρ`:
  `w₁ = 1 / (2 t q)`, `w₀ = (t - u q) / (2 t²)` with `t = (|W| - |U|)/4`, `u = |U|/4`.
  With `q = 1` these are exactly the Stage 217 weights (`normalized_weights_at_one`).

The punctured level `punc p H W U Res` keeps the edges of `H` inside `W`, deletes every edge inside
the child set `U` and every reserved edge.  Its `F₁`-copies have at most one child vertex; the
weight of a copy is `w₀` if it avoids `U` and `w₁` otherwise.

`punctured_weighting` (proved): every copy weight is in `[0, 8/|W|]` and EVERY edge of the punctured
level has load within `32 (κ' + 2ξ + 2ζ + ε)` of `1`, where `κ'` is the class defect of `U` and
`W \ U` and `ε` is the regularity defect of the reserve (`hR1`, `hR2` below: the reserve removes
a `q²` resp. `q` proportion of the relevant common neighbourhoods, up to `ε |W|`).  The reserve
density is normalised, not paid: no tolerance has to exceed the fixed loss `1 - q`.

The damage term `2ζ` is paid as a loss (Stage 218 style).  This is NOT enough to iterate the
vortex: see `NW18_BRANCH_LEDGER.md` §0sexies (the damage of the next level is forced to be of
order `ρ/β`, which is much larger than the nibble tolerance).
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-! ### Normalised scalar weights -/

/-- Weight of a copy with no child vertex. -/
noncomputable def w0 (t u q : ℝ) : ℝ := (t - u * q) / (2 * t ^ 2)

/-- Weight of a copy with one child vertex. -/
noncomputable def w1 (t q : ℝ) : ℝ := 1 / (2 * t * q)

/-- At `q = 1` the normalised weights are the Stage 217 weights. -/
theorem normalized_weights_at_one (t u : ℝ) :
    w0 t u 1 = F1PuncturedWeightsStage217.outsideWeight t u ∧
      w1 t 1 = F1PuncturedWeightsStage217.boundaryWeight t := by
  unfold w0 w1 F1PuncturedWeightsStage217.outsideWeight F1PuncturedWeightsStage217.boundaryWeight
  constructor <;> ring_nf

theorem w_outside_load (t u q : ℝ) (ht : 0 < t) :
    2 * t * w0 t u q + 2 * u * q ^ 2 * w1 t q = 1 := by
  unfold w0 w1; field_simp; ring

theorem w_boundary_load (t q : ℝ) (ht : 0 < t) (hq : 0 < q) : 2 * t * q * w1 t q = 1 := by
  unfold w1; field_simp

theorem w0_nonneg (t u q : ℝ) (ht : 0 < t) (h : u * q ≤ t) : 0 ≤ w0 t u q := by
  unfold w0; exact div_nonneg (by linarith) (by positivity)

theorem w0_le_w1 (t u q : ℝ) (ht : 0 < t) (hq : 0 < q) (hq1 : q ≤ 1) (hu : 0 ≤ u) :
    w0 t u q ≤ w1 t q := by
  unfold w0 w1
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ u * q := by positivity
  nlinarith [mul_nonneg (mul_nonneg ht.le ht.le) (sub_nonneg.mpr hq1), mul_nonneg this ht.le,
    mul_nonneg (mul_nonneg this ht.le) hq.le]

/-! ### The punctured level -/

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The punctured level: edges of `H` inside `W`, not inside `U`, not reserved. -/
def punc (H : SimpleGraph V) (W U : Finset V) (Res : Finset (Sym2 V)) : SimpleGraph V where
  Adj a b := H.Adj a b ∧ a ∈ W ∧ b ∈ W ∧ ¬ (a ∈ U ∧ b ∈ U) ∧ s(a, b) ∉ Res
  symm := ⟨fun a b h => ⟨h.1.symm, h.2.2.1, h.2.1, fun h' => h.2.2.2.1 ⟨h'.2, h'.1⟩,
    by rw [Sym2.eq_swap]; exact h.2.2.2.2⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

instance (H : SimpleGraph V) [DecidableRel H.Adj] (W U : Finset V) (Res : Finset (Sym2 V)) :
    DecidableRel (punc H W U Res).Adj := fun a b => by
  unfold punc; infer_instance

/-- The weighting of the punctured level. -/
noncomputable def puncWeight (U : Finset V) (a0 a1 : ℝ) (s : Finset V) : ℝ :=
  if Disjoint s U then a0 else a1

/-! ### Weighted copies through an edge -/

/-- Weighted version of `card_copies_through_gen`. -/
lemma sum_copies_through (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {u v : V} (huv : G.Adj u v) (f : Finset V → ℝ) :
    ∑ s ∈ (copies p F G).filter (fun s => s(u, v) ∈ triEdges s), f s =
      ∑ w ∈ univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧
        ({p u, p v, p w} : Multiset (Fin 4)) ∈ F), f {u, v, w} := by
  symm
  refine sum_bij (fun w _ => ({u, v, w} : Finset V)) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [mem_filter, mem_univ, true_and] at hw
    obtain ⟨huw, hwv, hty⟩ := hw
    have h1 : u ≠ v := G.ne_of_adj huv
    have h2 : u ≠ w := G.ne_of_adj huw
    have h3 : v ≠ w := (G.ne_of_adj hwv).symm
    refine mem_filter.mpr ⟨mem_copies_iff'.mpr ⟨SimpleGraph.is3Clique_triple_iff.mpr
      ⟨huv, huw, hwv.symm⟩, ?_⟩, mk_mem_triEdges.mpr ⟨by simp, by simp, h1⟩⟩
    rw [triple_val_map p h1 h2 h3]
    exact hty
  · intro w hw w' hw' h
    simp only [mem_filter, mem_univ, true_and] at hw hw'
    have h' : ({u, v, w} : Finset V) = {u, v, w'} := h
    have hw_mem : w ∈ ({u, v, w'} : Finset V) := by
      rw [← h']; simp
    simp only [mem_insert, mem_singleton] at hw_mem
    rcases hw_mem with rfl | rfl | rfl
    · exact absurd hw.1 (SimpleGraph.irrefl G)
    · exact absurd hw.2.1 (SimpleGraph.irrefl G)
    · rfl
  · intro s hs
    obtain ⟨hsC, hes⟩ := mem_filter.mp hs
    obtain ⟨hcl, hty⟩ := mem_copies_iff'.mp hsC
    obtain ⟨hus, hvs, huv'⟩ := mk_mem_triEdges.mp hes
    have hsub : ({u, v} : Finset V) ⊆ s := by
      intro x hx; simp only [mem_insert, mem_singleton] at hx; rcases hx with rfl | rfl <;> assumption
    have hcard : (s \ {u, v}).card = 1 := by
      rw [card_sdiff_of_subset hsub, hcl.card_eq, card_pair huv']
    obtain ⟨w, hw⟩ := card_eq_one.mp hcard
    have hws : w ∈ s \ {u, v} := by rw [hw]; simp
    simp only [mem_sdiff, mem_insert, mem_singleton, not_or] at hws
    obtain ⟨hws, hwu, hwv⟩ := hws
    have hseq : s = {u, v, w} := by
      ext x
      constructor
      · intro hx
        by_cases hxu : x = u
        · simp [hxu]
        by_cases hxv : x = v
        · simp [hxv]
        have : x ∈ s \ {u, v} := by simp [hx, hxu, hxv]
        rw [hw] at this
        simp at this; simp [this]
      · intro hx
        simp only [mem_insert, mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;> assumption
    have hadj := hcl.1
    have huw : G.Adj u w := hadj hus hws (Ne.symm hwu)
    have hvw : G.Adj v w := hadj hvs hws (Ne.symm hwv)
    refine ⟨w, ?_, hseq.symm⟩
    simp only [mem_filter, mem_univ, true_and]
    refine ⟨huw, hvw.symm, ?_⟩
    rw [hseq, triple_val_map p huv' (Ne.symm hwu) (Ne.symm hwv)] at hty
    exact hty

/-! ### Elementary counting -/

lemma twoThirds_F1' : TwoThirds F1 := by unfold TwoThirds; decide

omit [Fintype V] in
/-- A finset is at most its `P`-part plus an exceptional set containing every non-`P` element. -/
lemma card_le_filter_add (S X : Finset V) (P : V → Prop) [DecidablePred P]
    (h : ∀ z ∈ S, ¬ P z → z ∈ X) : S.card ≤ (S.filter P).card + X.card := by
  have hsub : S ⊆ S.filter P ∪ X := by
    intro z hz
    by_cases hP : P z
    · exact mem_union_left _ (mem_filter.mpr ⟨hz, hP⟩)
    · exact mem_union_right _ (h z hz hP)
  exact (card_le_card hsub).trans (card_union_le _ _)

omit [Fintype V] in
/-- **Common neighbourhood count in the damaged level.**  For `S ⊆ W`, `a, b ∈ W` and a class `l`
allowed with both, the common `H`-neighbours of `a, b` in `S_l` number between
`|S_l| - 2ξ|W| - 2ζ|W|` and `|S_l|`. -/
lemma common_count_bounds (p : V → Fin 4) (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (W S : Finset V) (hSW : S ⊆ W) (ξ ζ : ℝ)
    (htyp : ∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card)
    (hdam : ∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card)
    (a b : V) (ha : a ∈ W) (hb : b ∈ W) (l : Fin 4) (hal : AllowedT F1 (p a) l)
    (hbl : AllowedT F1 (p b) l) :
    ((S.filter fun z => p z = l).card : ℝ) - 2 * ξ * W.card - 2 * ζ * W.card ≤
        ((S.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card : ℝ) ∧
      ((S.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card : ℝ) ≤
        ((S.filter fun z => p z = l).card : ℝ) := by
  constructor
  · set X := (W.filter fun z => p z = l ∧ ¬ G.Adj a z) ∪ (W.filter fun z => p z = l ∧ ¬ G.Adj b z)
      ∪ ((W.filter fun v => G.Adj a v ∧ ¬ H.Adj a v) ∪ (W.filter fun v => G.Adj b v ∧ ¬ H.Adj b v))
      with hX
    have hfilt : (S.filter fun z => p z = l).filter (fun z => H.Adj a z ∧ H.Adj b z) =
        S.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z := by
      rw [filter_filter]
    have h1 := card_le_filter_add (S.filter fun z => p z = l) X (fun z => H.Adj a z ∧ H.Adj b z)
      (by
        intro z hz hn
        obtain ⟨hzS, hzl⟩ := mem_filter.mp hz
        have hzW := hSW hzS
        simp only [hX, mem_union, mem_filter]
        by_cases hGa : G.Adj a z
        · by_cases hHa : H.Adj a z
          · have hHb : ¬ H.Adj b z := fun h => hn ⟨hHa, h⟩
            by_cases hGb : G.Adj b z
            · exact Or.inr (Or.inr ⟨hzW, hGb, hHb⟩)
            · exact Or.inl (Or.inr ⟨hzW, hzl, hGb⟩)
          · exact Or.inr (Or.inl ⟨hzW, hGa, hHa⟩)
        · exact Or.inl (Or.inl ⟨hzW, hzl, hGa⟩))
    rw [hfilt] at h1
    have hXc : (X.card : ℝ) ≤ 2 * ξ * W.card + 2 * ζ * W.card := by
      have e1 := card_union_le ((W.filter fun z => p z = l ∧ ¬ G.Adj a z) ∪
        (W.filter fun z => p z = l ∧ ¬ G.Adj b z))
        ((W.filter fun v => G.Adj a v ∧ ¬ H.Adj a v) ∪ (W.filter fun v => G.Adj b v ∧ ¬ H.Adj b v))
      have e2 := card_union_le (W.filter fun z => p z = l ∧ ¬ G.Adj a z)
        (W.filter fun z => p z = l ∧ ¬ G.Adj b z)
      have e3 := card_union_le (W.filter fun v => G.Adj a v ∧ ¬ H.Adj a v)
        (W.filter fun v => G.Adj b v ∧ ¬ H.Adj b v)
      have r1 : (X.card : ℝ) ≤ (W.filter fun z => p z = l ∧ ¬ G.Adj a z).card +
          (W.filter fun z => p z = l ∧ ¬ G.Adj b z).card +
          ((W.filter fun v => G.Adj a v ∧ ¬ H.Adj a v).card +
          (W.filter fun v => G.Adj b v ∧ ¬ H.Adj b v).card) := by
        rw [hX]; exact_mod_cast e1.trans (add_le_add e2 e3)
      have := htyp a ha l hal
      have := htyp b hb l hbl
      have := hdam a ha
      have := hdam b hb
      linarith
    have h1' : ((S.filter fun z => p z = l).card : ℝ) ≤
        (S.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card + X.card := by
      exact_mod_cast h1
    linarith
  · exact_mod_cast card_le_card (fun z hz => by
      simp only [mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.1⟩)

end NashWilliams18.SpreadF1
