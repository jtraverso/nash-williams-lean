/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.MatchedQuotaStage140
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-! # Nonnegative matching quotas from minimum degree three quarters

A cut uses at most the product of its two sides. The degree-sum identity
therefore pays all three matching quotas simultaneously.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CutSurplusStage140

open Finset MatchedQuotaStage140

variable {V : Type*} [Fintype V]

theorem cut_product_bound (p : V → Fin 4) (E : Finset (Sym2 V)) (i : Fin 3) :
    (cuts p E i).card ≤
      (univ.filter fun v => side i (p v) = 0).card *
      (univ.filter fun v => side i (p v) = 1).card := by
  classical
  let S := univ.filter fun v => side i (p v) = 0
  let T := univ.filter fun v => side i (p v) = 1
  let R := (S ×ˢ T).image fun ab => s(ab.1, ab.2)
  have hsub : cuts p E i ⊆ R := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hne := (mem_filter.mp he).2
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, Function.comp_apply] at hne
      have hcases (v : V) : side i (p v) = 0 ∨ side i (p v) = 1 := by
        have h := (side i (p v)).isLt
        omega
      rcases hcases a with ha | ha <;> rcases hcases b with hb | hb
      · exact False.elim (hne (ha.trans hb.symm))
      · apply mem_image.mpr
        exact ⟨(a, b), mem_product.mpr
          ⟨mem_filter.mpr ⟨mem_univ _, ha⟩, mem_filter.mpr ⟨mem_univ _, hb⟩⟩, rfl⟩
      · apply mem_image.mpr
        exact ⟨(b, a), mem_product.mpr
          ⟨mem_filter.mpr ⟨mem_univ _, hb⟩, mem_filter.mpr ⟨mem_univ _, ha⟩⟩,
          Sym2.eq_swap⟩
      · exact False.elim (hne (ha.trans hb.symm))
  exact (card_le_card hsub).trans (card_image_le.trans_eq (card_product S T))

theorem side_cards_sum (p : V → Fin 4) (i : Fin 3) :
    (univ.filter fun v => side i (p v) = 0).card +
      (univ.filter fun v => side i (p v) = 1).card = Fintype.card V := by
  have heq : (univ.filter fun v : V => ¬ side i (p v) = 0) =
      (univ.filter fun v => side i (p v) = 1) := by
    apply filter_congr
    intro v _
    have h := (side i (p v)).isLt
    omega
  have h := card_filter_add_card_filter_not (s := (univ : Finset V))
    (fun v => side i (p v) = 0)
  simpa only [heq, card_univ] using h

theorem cut_square_bound (p : V → Fin 4) (E : Finset (Sym2 V)) (i : Fin 3) :
    4 * (cuts p E i).card ≤ (Fintype.card V) ^ 2 := by
  have hp := cut_product_bound p E i
  have hs := side_cards_sum p i
  set a := (univ.filter fun v => side i (p v) = 0).card
  set b := (univ.filter fun v => side i (p v) = 1).card
  have hp' : (cuts p E i).card ≤ a * b := hp
  have hs' : a + b = Fintype.card V := hs
  have hpz : ((cuts p E i).card : ℤ) ≤ (a : ℤ) * b := by exact_mod_cast hp'
  have hsz : (a : ℤ) + b = Fintype.card V := by exact_mod_cast hs'
  have h : 4 * ((cuts p E i).card : ℤ) ≤ (Fintype.card V : ℤ) ^ 2 := by
    nlinarith [sq_nonneg ((a : ℤ) - b)]
  exact_mod_cast h

theorem surplus_of_degree (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdegree : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v) (i : Fin 3) :
    3 * (cuts p G.edgeFinset i).card ≤ 2 * G.edgeFinset.card := by
  classical
  have hsum := sum_le_sum (s := (univ : Finset V)) (fun v _ => hdegree v)
  simp only [sum_const, card_univ, smul_eq_mul, ← mul_sum,
    G.sum_degrees_eq_twice_card_edges] at hsum
  have hcut := cut_square_bound p G.edgeFinset i
  nlinarith

theorem surplus_of_real_degree (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hdegree : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v) (i : Fin 3) :
    3 * (cuts p G.edgeFinset i).card ≤ 2 * G.edgeFinset.card := by
  apply surplus_of_degree p G
  intro v
  have h := hdegree v
  have h' : (3 : ℝ) * Fintype.card V ≤ 4 * G.degree v := by linarith
  exact_mod_cast h'

end PartitionedTriangleAbsorption.CutSurplusStage140
