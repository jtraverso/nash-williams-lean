/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.Perturb
public import RequestProject.Fractional.Farkas

@[expose] public section

/-!
# Fractional Nash-Williams via Farkas (Theorem 1.4)

Combining the dual statement `covered_sum_nonneg` (Conjecture 4.5 under `δ ≥ 3n/4`) with
Farkas' lemma gives a fractional triangle decomposition.
-/

namespace NashWilliams.Frac
open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

lemma triangle_ordered_sum (y : V × V → ℝ) {a b c : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (hbc : G.Adj b c) :
    ∑ p : V × V, (if G.Adj p.1 p.2 ∧ p.1 ∈ ({a, b, c} : Finset V) ∧ p.2 ∈ ({a, b, c} : Finset V)
      then (1 : ℝ) else 0) * y p =
      (y (a, b) + y (b, a)) + (y (a, c) + y (c, a)) + (y (b, c) + y (c, b)) := by
  have h1 := hab.ne; have h2 := hac.ne; have h3 := hbc.ne
  rw [Fintype.sum_prod_type]
  simp only [ite_mul, one_mul, zero_mul]
  have : ∀ u, ∑ v, (if G.Adj u v ∧ u ∈ ({a, b, c} : Finset V) ∧ v ∈ ({a, b, c} : Finset V)
      then y (u, v) else 0) = if u ∈ ({a, b, c} : Finset V) then
        ∑ v ∈ ({a, b, c} : Finset V), (if G.Adj u v then y (u, v) else 0) else 0 := by
    intro u
    split_ifs with hu
    · rw [← sum_filter, ← sum_filter]
      congr 1; ext v; simp [hu, and_comm]
    · simp [hu]
  simp only [this]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]
  have ha : a ∉ ({b, c} : Finset V) := by simp [h1, h2]
  have hb : b ∉ ({c} : Finset V) := by simp [h3]
  simp only [sum_insert ha, sum_insert hb, sum_singleton]
  simp [hab, hac, hbc, hab.symm, hac.symm, hbc.symm]
  ring


/-- Dual form via Farkas: under `3n ≤ 4δ`, there are nonnegative triangle weights giving every
edge total weight `1`. -/
theorem exists_fractional_weights (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree) :
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
    have hc := covered_sum_nonneg G hδ φ hcov
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
    fun t => by dsimp only; split_ifs; exacts [hx _, le_rfl], fun u v huv => ?_⟩
  have hev := congrFun hxb (u, v)
  simp only [hA, hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, huv, true_and,
    if_true] at hev
  rw [← hev, sum_filter, ← sum_coe_sort (G.cliqueFinset 3)]
  refine sum_congr rfl fun t _ => ?_
  simp only [t.2, dite_true]
  split_ifs <;> simp

end NashWilliams.Frac
