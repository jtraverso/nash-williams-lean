/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NashWilliamsBasic

/-!
# Farkas' lemma for triangle decompositions, for arbitrary graphs

`exists_fractional_weights_of_dual` is the dual form of Lemma 2.2 / Lemma 4.4 of the paper
without any degree assumption; `hasFrac_of_good` combines it with the perturbation of
Proposition 4.7: if every nonzero untied triangle-covered weighting has nonnegative value, the
graph has a fractional triangle decomposition.
-/

namespace NashWilliams.Frac
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Dual form via Farkas, for an arbitrary graph: if every triangle-covered edge weighting has
nonnegative value, then there are nonnegative triangle weights giving every edge total weight
`1`. -/
theorem exists_fractional_weights_of_dual
    (hdual : ∀ φ : Sym2 V → ℝ, (∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
      0 ≤ φ s(a, b) + φ s(a, c) + φ s(b, c)) →
      0 ≤ ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0)) :
    ∃ w : Finset V → ℝ, (∀ t, 0 ≤ w t) ∧
      ∀ u v, G.Adj u v → ∑ t ∈ G.cliqueFinset 3 with u ∈ t ∧ v ∈ t, w t = 1 := by
  set A : {t // t ∈ G.cliqueFinset 3} → V × V → ℝ :=
    fun t p => if G.Adj p.1 p.2 ∧ p.1 ∈ t.1 ∧ p.2 ∈ t.1 then 1 else 0 with hA
  set b : V × V → ℝ := fun p => if G.Adj p.1 p.2 then 1 else 0 with hb
  obtain ⟨x, hx, hxb⟩ := farkas A b (by
    intro y hy
    set φ : Sym2 V → ℝ := Sym2.lift ⟨fun a b => y (a, b) + y (b, a), fun a b => add_comm _ _⟩
    have hcov : ∀ a b c, G.Adj a b → G.Adj a c → G.Adj b c →
        0 ≤ φ s(a, b) + φ s(a, c) + φ s(b, c) := by
      intro a b c hab hac hbc
      have hmem : ({a, b, c} : Finset V) ∈ G.cliqueFinset 3 := by
        rw [SimpleGraph.mem_cliqueFinset_iff, SimpleGraph.is3Clique_triple_iff]
        exact ⟨hab, hac, hbc⟩
      have := hy ⟨_, hmem⟩
      simp only [hA] at this
      rw [triangle_ordered_sum G y hab hac hbc] at this
      simpa [φ] using this
    have hc := hdual φ hcov
    have hsym : ∑ a, ∑ c, (if G.Adj a c then y (c, a) else 0) =
        ∑ a, ∑ c, (if G.Adj a c then y (a, c) else 0) := by
      rw [Finset.sum_comm]
      refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
      simp only [G.adj_comm]
    have hsplit : ∑ a, ∑ c, (if G.Adj a c then φ s(a, c) else 0) =
        ∑ a, ∑ c, (if G.Adj a c then y (a, c) else 0) +
          ∑ a, ∑ c, (if G.Adj a c then y (c, a) else 0) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [← sum_add_distrib]
      refine sum_congr rfl fun c _ => ?_
      split_ifs <;> simp [φ]
    have hgoal : ∑ k, b k * y k = ∑ a, ∑ c, (if G.Adj a c then y (a, c) else 0) := by
      rw [Fintype.sum_prod_type]
      simp [hb, ite_mul]
    rw [hgoal]
    linarith)
  refine ⟨fun t => if h : t ∈ G.cliqueFinset 3 then x ⟨t, h⟩ else 0,
    fun t => by dsimp (config := { failIfUnchanged := false }) only; split_ifs; exacts [hx _, le_rfl], fun u v huv => ?_⟩
  have hev := congrFun hxb (u, v)
  simp only [hA, hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, huv, true_and,
    if_true] at hev
  rw [← hev, sum_filter, ← sum_coe_sort (G.cliqueFinset 3)]
  refine sum_congr rfl fun t _ => ?_
  simp only [t.2, dite_true]
  split_ifs <;> simp

/-- If every good (nonzero, untied, triangle-covered) weighting has nonnegative value, then
`G` has a fractional triangle decomposition. -/
theorem hasFrac_of_good
    (h : ∀ φ : Sym2 V → ℝ, GoodWeighting G φ →
      0 ≤ ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0)) :
    NashWilliams.HasFractionalTriangleDecomposition G := by
  obtain ⟨w, hw0, hw⟩ := exists_fractional_weights_of_dual G (fun φ hcov => by
    by_contra hneg
    push_neg at hneg
    obtain ⟨ψ, hψ, hψneg⟩ := exists_good_perturbation G φ hcov hneg
    exact absurd (h ψ hψ) (not_le.2 hψneg))
  exact ⟨w, hw0, hw⟩

end NashWilliams.Frac
