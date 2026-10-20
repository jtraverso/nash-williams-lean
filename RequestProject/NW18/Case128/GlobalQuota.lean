/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case128.Ledger

/-!
# Case (5): lower bounds for the matched-triangle quotas

This file contains the counting behind Claims 12.8.6 and 12.8.7 and Proposition 15.25.

* `cut_add_farMissing_le` and `sixQuota_ge_sum`: the quota `2|E| − 3 cut_i(E)` is at least
  `Σ_{v ∈ S} (d(v) − 3n/4 + 3 m̄_i(v))`, where `m̄_i(v)` counts the non-neighbours of `v` outside
  `S` on the other side of the `i`-th bipartition (the identity in the proof of Claim 12.8.6).
* `quota_slack`: for a vertex of a locally optimal partition, this per-vertex contribution
  exceeds `6 (d₀(v) + d_i(v) − d(v)/2)` by a linear amount (the role of Proposition 15.25(iii)).
* `two_large`: for a vertex with large internal degree, two of the three contributions are
  linear (Proposition 15.25(v)), and `exists_large_pair` turns this into two large quotas
  (Claim 12.8.7).
-/

namespace NashWilliams18.C128

open Finset PartitionedTriangleAbsorption MatchedQuotaStage140 ExceptionalQuotaStage142
open GraphStarInventoryStage144 ClassRepresentativesStage65

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Non-neighbours of `v` outside `S` on the other side of the `i`-th bipartition. -/
def farMissing (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (S : Finset V)
    (i : Fin 3) (v : V) : Finset V :=
  univ.filter fun w => w ∉ S ∧ side i (p w) ≠ side i (p v) ∧ ¬ G.Adj v w

/-- Cut edges and missing cross pairs at `S` together fit into the product of the two sides. -/
theorem cut_add_farMissing_le (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (i : Fin 3) :
    (cuts p G.edgeFinset i).card + ∑ v ∈ S, (farMissing G p S i v).card ≤
      (univ.filter fun v => side i (p v) = 0).card *
        (univ.filter fun v => side i (p v) = 1).card := by
  classical
  let X := univ.filter fun v => side i (p v) = 0
  let Y := univ.filter fun v => side i (p v) = 1
  let R := (X ×ˢ Y).image fun ab => s(ab.1, ab.2)
  have hcases (v : V) : side i (p v) = 0 ∨ side i (p v) = 1 := by
    have h := (side i (p v)).isLt
    omega
  have hR : ∀ a b, side i (p a) ≠ side i (p b) → s(a, b) ∈ R := by
    intro a b hne
    rcases hcases a with ha | ha <;> rcases hcases b with hb | hb
    · exact False.elim (hne (ha.trans hb.symm))
    · exact mem_image.mpr ⟨(a, b), mem_product.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, ha⟩, mem_filter.mpr ⟨mem_univ _, hb⟩⟩, rfl⟩
    · exact mem_image.mpr ⟨(b, a), mem_product.mpr
        ⟨mem_filter.mpr ⟨mem_univ _, hb⟩, mem_filter.mpr ⟨mem_univ _, ha⟩⟩, Sym2.eq_swap⟩
    · exact False.elim (hne (ha.trans hb.symm))
  let M := S.biUnion fun v => (farMissing G p S i v).image fun w => s(v, w)
  have hcut : cuts p G.edgeFinset i ⊆ R := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hne := (mem_filter.mp he).2
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, Function.comp_apply] at hne
      exact hR a b hne
  have hM : M ⊆ R := by
    intro e he
    obtain ⟨v, -, he⟩ := mem_biUnion.mp he
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he
    have hw' := (mem_filter.mp hw).2
    exact hR v w (Ne.symm hw'.2.1)
  have hdisj : Disjoint (cuts p G.edgeFinset i) M := by
    refine disjoint_left.mpr fun e he heM => ?_
    obtain ⟨v, -, he'⟩ := mem_biUnion.mp heM
    obtain ⟨w, hw, rfl⟩ := mem_image.mp he'
    have hG : G.Adj v w := by simpa using (mem_filter.mp he).1
    exact (mem_filter.mp hw).2.2.2 hG
  have hMcard : M.card = ∑ v ∈ S, (farMissing G p S i v).card := by
    rw [card_biUnion]
    · refine sum_congr rfl fun v _ => card_image_of_injective _ ?_
      intro w w' h
      rcases Sym2.eq_iff.mp h with ⟨-, h'⟩ | ⟨h1, h2⟩
      · exact h'
      · exact h2.trans h1
    · intro v hv v' hv' hvv'
      refine disjoint_left.mpr fun e he he' => hvv' ?_
      obtain ⟨w, hw, rfl⟩ := mem_image.mp he
      obtain ⟨w', hw', h⟩ := mem_image.mp he'
      have hwS := (mem_filter.mp hw).2.1
      have hwS' := (mem_filter.mp hw').2.1
      rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact h1.symm
      · exact absurd (h1 ▸ (mem_coe.mp hv')) hwS
  have hcard : (cuts p G.edgeFinset i).card + M.card ≤ R.card := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_card (union_subset hcut hM)
  rw [← hMcard]
  exact hcard.trans (card_image_le.trans_eq (card_product X Y))

/-- **The quota identity of Claim 12.8.6** (as an inequality).  If `δ(G) ≥ 3n/4`, then
`2|E| − 3 cut_i(E) ≥ Σ_{v ∈ S} (d(v) − 3n/4 + 3 m̄_i(v))`. -/
theorem sixQuota_ge_sum (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (i : Fin 3)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v) :
    ∑ v ∈ S, ((G.degree v : ℝ) - 3 / 4 * Fintype.card V +
        3 * (farMissing G p S i v).card) ≤ (sixQuota p G.edgeFinset i : ℝ) := by
  classical
  set n := Fintype.card V
  have hcut := cut_add_farMissing_le G p S i
  have hsides := CutSurplusStage140.side_cards_sum p i
  set a := (univ.filter fun v => side i (p v) = 0).card
  set b := (univ.filter fun v => side i (p v) = 1).card
  have hcutR : ((cuts p G.edgeFinset i).card : ℝ) +
      ∑ v ∈ S, ((farMissing G p S i v).card : ℝ) ≤ (a : ℝ) * b := by
    exact_mod_cast hcut
  have hab : (a : ℝ) + b = n := by exact_mod_cast hsides
  have hprod : 4 * ((a : ℝ) * b) ≤ (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℝ) - b)]
  have hsum : ∑ v, (G.degree v : ℝ) = 2 * G.edgeFinset.card := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hsplit : ∑ v, (G.degree v : ℝ) =
      ∑ v ∈ S, (G.degree v : ℝ) + ∑ v ∈ Sᶜ, (G.degree v : ℝ) := by
    rw [← sum_add_sum_compl S]
  have hcompl : ((Sᶜ).card : ℝ) * (3 / 4 * n) ≤ ∑ v ∈ Sᶜ, (G.degree v : ℝ) := by
    have := sum_le_sum (s := Sᶜ) (fun v _ => hdeg v)
    simpa [mul_comm] using this
  have hScard : ((Sᶜ).card : ℝ) = n - S.card := by
    rw [card_compl]
    rw [Nat.cast_sub (card_le_univ S)]
  have hsix : (sixQuota p G.edgeFinset i : ℝ) =
      2 * G.edgeFinset.card - 3 * (cuts p G.edgeFinset i).card := by
    simp [sixQuota]
  rw [hsix]
  have hlhs : ∑ v ∈ S, ((G.degree v : ℝ) - 3 / 4 * n + 3 * (farMissing G p S i v).card) =
      ∑ v ∈ S, (G.degree v : ℝ) - S.card * (3 / 4 * n) +
        3 * ∑ v ∈ S, ((farMissing G p S i v).card : ℝ) := by
    simp only [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    ring
  rw [hlhs]
  rw [hScard] at hcompl
  nlinarith

/-- Own class and the `i`-th partner class together carry the same-side neighbours. -/
lemma farMissing_ge (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (S : Finset V)
    (i : Fin 3) (v : V) :
    (Fintype.card V : ℝ) - (classSet p (p v)).card - (classSet p (partner i (p v))).card -
        (G.degree v - classLoad p G v (p v) - classLoad p G v (partner i (p v))) - S.card ≤
      (farMissing G p S i v).card := by
  classical
  set O := univ.filter fun w => side i (p w) ≠ side i (p v)
  -- the same side of `v` is the union of its class and the `i`-th partner class
  have hsame : (univ.filter fun w => ¬ side i (p w) ≠ side i (p v)) =
      classSet p (p v) ∪ classSet p (partner i (p v)) := by
    ext w
    simp only [not_not, mem_filter, mem_univ, true_and, mem_union, classSet]
    rw [same_labels]
  have hdisj : Disjoint (classSet p (p v)) (classSet p (partner i (p v))) := by
    refine disjoint_left.mpr fun w h1 h2 => ?_
    simp only [classSet, mem_filter, mem_univ, true_and] at h1 h2
    exact partner_ne i (p v) (h2.symm.trans h1)
  have hO : O.card + (classSet p (p v)).card + (classSet p (partner i (p v))).card =
      Fintype.card V := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset V))
      (fun w => side i (p w) ≠ side i (p v))
    rw [hsame, card_union_of_disjoint hdisj, card_univ] at h
    change O.card + _ = _ at h
    omega
  -- neighbours on the other side
  have hN : (O.filter fun w => G.Adj v w).card + classLoad p G v (p v) +
      classLoad p G v (partner i (p v)) = G.degree v := by
    have h1 := same_inventory p G v i
    rw [same_load_neighbor] at h1
    have h2 := card_filter_add_card_filter_not (s := G.neighborFinset v)
      (fun w => (side i ∘ p) w = (side i ∘ p) v)
    rw [G.card_neighborFinset_eq_degree] at h2
    have h3 : (O.filter fun w => G.Adj v w) =
        (G.neighborFinset v).filter (fun w => ¬ (side i ∘ p) w = (side i ∘ p) v) := by
      ext w
      simp [O, and_comm]
    rw [h3]
    omega
  -- the non-neighbours on the other side lie in `farMissing ∪ S`
  have hsub : O.filter (fun w => ¬ G.Adj v w) ⊆ farMissing G p S i v ∪ S := by
    intro w hw
    simp only [O, mem_filter, mem_univ, true_and] at hw
    by_cases hwS : w ∈ S
    · exact mem_union_right _ hwS
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hwS, hw.1, hw.2⟩)
  have hsplit := card_filter_add_card_filter_not (s := O) (fun w => G.Adj v w)
  have hle := (card_le_card hsub).trans (card_union_le _ _)
  have hR : ((O.filter fun w => G.Adj v w).card : ℝ) + (O.filter fun w => ¬ G.Adj v w).card =
      O.card := by exact_mod_cast hsplit
  have hOR : (O.card : ℝ) + (classSet p (p v)).card + (classSet p (partner i (p v))).card =
      Fintype.card V := by exact_mod_cast hO
  have hNR : ((O.filter fun w => G.Adj v w).card : ℝ) + classLoad p G v (p v) +
      classLoad p G v (partner i (p v)) = G.degree v := by exact_mod_cast hN
  have hleR : ((O.filter fun w => ¬ G.Adj v w).card : ℝ) ≤
      (farMissing G p S i v).card + S.card := by exact_mod_cast hle
  linarith

/-- Non-neighbours in a class on the other side. -/
lemma farMissing_ge_class (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
    (S : Finset V) (i ℓ : Fin 3) (h : i ≠ ℓ) (v : V) :
    ((classSet p (partner ℓ (p v))).card : ℝ) - classLoad p G v (partner ℓ (p v)) - S.card ≤
      (farMissing G p S i v).card := by
  classical
  set K := classSet p (partner ℓ (p v))
  have hload : classLoad p G v (partner ℓ (p v)) = (K.filter fun w => G.Adj v w).card := by
    unfold classLoad
    congr 1
    ext w
    simp [K, classSet, and_comm]
  have hsub : K.filter (fun w => ¬ G.Adj v w) ⊆ farMissing G p S i v ∪ S := by
    intro w hw
    simp only [K, classSet, mem_filter, mem_univ, true_and] at hw
    by_cases hwS : w ∈ S
    · exact mem_union_right _ hwS
    · refine mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hwS, ?_, hw.2⟩)
      rw [hw.1]
      exact side_partner_ne i ℓ h (p v)
  have hsplit := card_filter_add_card_filter_not (s := K) (fun w => G.Adj v w)
  have hle := (card_le_card hsub).trans (card_union_le _ _)
  rw [← hload] at hsplit
  have h1 : (classLoad p G v (partner ℓ (p v)) : ℝ) + (K.filter fun w => ¬ G.Adj v w).card =
      K.card := by exact_mod_cast hsplit
  have h2 : ((K.filter fun w => ¬ G.Adj v w).card : ℝ) ≤
      (farMissing G p S i v).card + S.card := by exact_mod_cast hle
  linarith

omit [DecidableEq V] in
/-- Local optimality: the own class and one partner class carry at most `d(v) − 2 d₀(v)`. -/
lemma three_own_add_le (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hloc : ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j) (v : V) (i : Fin 3) :
    3 * classLoad p G v (p v) + classLoad p G v (partner i (p v)) ≤ G.degree v := by
  have h := degree_inventory p G v
  rw [Fin.sum_univ_three] at h
  have h0 := hloc v (partner 0 (p v))
  have h1 := hloc v (partner 1 (p v))
  have h2 := hloc v (partner 2 (p v))
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at * <;> omega

/-- **Per-vertex quota slack** (the role of Proposition 15.25(iii)).  For a vertex `v` of a
locally optimal partition whose classes have size at most `(1/4 + 8ρ) n`,
`6 (d₀(v) + d_i(v) − d(v)/2) + 6 (n/24 − 11ρn − |S|/2) ≤ d(v) − 3n/4 + 3 m̄_i(v)`. -/
theorem quota_slack (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (S : Finset V)
    (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hloc : ∀ v j, classLoad p G v (p v) ≤ classLoad p G v j)
    (hsize : ∀ j, ((classSet p j).card : ℝ) ≤ (1 / 4 + 8 * ρ) * Fintype.card V)
    (i : Fin 3) (v : V) :
    6 * ((classLoad p G v (p v) : ℝ) + classLoad p G v (partner i (p v)) -
        (G.degree v : ℝ) / 2) +
      6 * ((Fintype.card V : ℝ) / 24 - 11 * ρ * Fintype.card V - S.card / 2) ≤
      (G.degree v : ℝ) - 3 / 4 * Fintype.card V + 3 * (farMissing G p S i v).card := by
  have hF := farMissing_ge G p S i v
  have h3 : (3 * classLoad p G v (p v) + classLoad p G v (partner i (p v)) : ℝ) ≤
      G.degree v := by exact_mod_cast three_own_add_le p G hloc v i
  have hmi : (classLoad p G v (partner i (p v)) : ℝ) ≤
      (classSet p (partner i (p v))).card := by
    exact_mod_cast classLoad_le_class_card p G v (partner i (p v))
  have hs0 := hsize (p v)
  have hsi := hsize (partner i (p v))
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith

/-- **Two large contributions** (Proposition 15.25(v)).  If `v` has more than `τ n`
neighbours in its own class, then for all but at most one index `i` its contribution
`(d(v) − 3n/4 + 3 m̄_i(v))/6` is at least `τ n / 20`. -/
theorem two_large (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (S : Finset V)
    (ρ τ : ℝ) (v : V) (hdeg : (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (hlow : ∀ j, (1 / 4 - 24 * ρ) * Fintype.card V ≤ ((classSet p j).card : ℝ))
    (hm0 : τ * Fintype.card V < classLoad p G v (p v))
    (hsmall : 12 * ρ * Fintype.card V + S.card / 2 ≤ τ * Fintype.card V / 180) :
    ∃ ℓ : Fin 3, ∀ i, i ≠ ℓ → τ * Fintype.card V / 20 ≤
      ((G.degree v : ℝ) - 3 / 4 * Fintype.card V + 3 * (farMissing G p S i v).card) / 6 := by
  set n : ℝ := (Fintype.card V : ℝ)
  set m0 : ℝ := (classLoad p G v (p v) : ℝ)
  have hinv := degree_inventory p G v
  rw [Fin.sum_univ_three] at hinv
  have hinvR : m0 + (classLoad p G v (partner 0 (p v)) : ℝ) +
      classLoad p G v (partner 1 (p v)) + classLoad p G v (partner 2 (p v)) = G.degree v := by
    simp only [m0]; exact_mod_cast (by omega : classLoad p G v (p v) +
      classLoad p G v (partner 0 (p v)) + classLoad p G v (partner 1 (p v)) +
      classLoad p G v (partner 2 (p v)) = G.degree v)
  have hF0 : ∀ i, (0 : ℝ) ≤ (farMissing G p S i v).card := fun _ => Nat.cast_nonneg _
  by_cases hD : 2 * m0 / 3 ≤ (G.degree v : ℝ) - 3 / 4 * n
  · refine ⟨0, fun i _ => ?_⟩
    have := hF0 i
    nlinarith
  · push_neg at hD
    -- some partner class carries few neighbours
    have hex : ∃ ℓ : Fin 3, (classLoad p G v (partner ℓ (p v)) : ℝ) < n / 4 - m0 / 9 := by
      by_contra hne
      push_neg at hne
      have h0 := hne 0
      have h1 := hne 1
      have h2 := hne 2
      linarith
    obtain ⟨ℓ, hℓ⟩ := hex
    refine ⟨ℓ, fun i hi => ?_⟩
    have hc := farMissing_ge_class G p S i ℓ hi v
    have hl := hlow (partner ℓ (p v))
    have hm0' : τ * n < m0 := hm0
    have hD0 : (0 : ℝ) ≤ (G.degree v : ℝ) - 3 / 4 * n := by linarith
    nlinarith

omit [Fintype V] [DecidableEq V] in
/-- **Two large quotas** (Claim 12.8.7, pigeonhole step).  If every `v ∈ S` has two indices
with contribution at least `c ≥ 0`, then some index `ℓ₀` is such that the other two indices have
total contribution at least `|S| c / 3`. -/
theorem exists_large_pair (S : Finset V) (f : V → Fin 3 → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hf0 : ∀ v ∈ S, ∀ i, 0 ≤ f v i)
    (hf : ∀ v ∈ S, ∃ ℓ : Fin 3, ∀ i, i ≠ ℓ → c ≤ f v i) :
    ∃ ℓ₀ : Fin 3, ∀ i, i ≠ ℓ₀ → (S.card : ℝ) * c / 3 ≤ ∑ v ∈ S, f v i := by
  classical
  choose! ℓ hℓ using hf
  have hcard : ∑ k : Fin 3, ((S.filter fun v => ℓ v = k).card : ℝ) = S.card := by
    have := card_eq_sum_card_fiberwise (f := ℓ) (s := S) (t := univ)
      (fun _ _ => mem_coe.mpr (mem_univ _))
    exact_mod_cast this.symm
  rw [Fin.sum_univ_three] at hcard
  have hex : ∃ k : Fin 3, (S.card : ℝ) / 3 ≤ (S.filter fun v => ℓ v = k).card := by
    by_contra hne
    push_neg at hne
    have := hne 0; have := hne 1; have := hne 2
    linarith
  obtain ⟨k, hk⟩ := hex
  refine ⟨k, fun i hi => ?_⟩
  calc (S.card : ℝ) * c / 3 = (S.card : ℝ) / 3 * c := by ring
    _ ≤ (S.filter fun v => ℓ v = k).card * c := mul_le_mul_of_nonneg_right hk hc
    _ = ∑ v ∈ S.filter (fun v => ℓ v = k), c := by simp
    _ ≤ ∑ v ∈ S.filter (fun v => ℓ v = k), f v i := by
        apply sum_le_sum
        intro v hv
        obtain ⟨hvS, hvk⟩ := mem_filter.mp hv
        exact hℓ v hvS i (hvk ▸ hi)
    _ ≤ ∑ v ∈ S, f v i :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun v hv _ => hf0 v hv i)

/-- The column inequality: positive parts of lower bounds with a uniform linear slack below
contributions in `[0, n]` use at most `29/30` of the total contribution. -/
theorem column_bound {W : Type*} (S : Finset W) (κ lo : W → ℝ) (n σ : ℝ)
    (hσ : n / 30 ≤ σ) (hκ0 : ∀ v ∈ S, 0 ≤ κ v) (hκn : ∀ v ∈ S, κ v ≤ n)
    (hlo : ∀ v ∈ S, lo v ≤ κ v - σ) :
    ∑ v ∈ S, max 0 (lo v) ≤ 29 / 30 * ∑ v ∈ S, κ v := by
  rw [mul_sum]
  apply sum_le_sum
  intro v hv
  have h1 := hκ0 v hv
  have h2 := hκn v hv
  have h3 := hlo v hv
  have h4 : κ v / 30 ≤ n / 30 := by linarith
  apply max_le <;> linarith

end NashWilliams18.C128
