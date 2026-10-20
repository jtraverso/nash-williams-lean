/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-! Ingredients only: numerical margins and a triangle-free link bound.
The connectivity theorem for the opposite-edge graph is not asserted here. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.RobustTransportMarginsStage258

open Finset

theorem parameter_bounds (a e b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsmall : 1000000 * e ≤ a * a) (hb : a * b = 400 * e) :
    e ≤ 1 / 1000000 ∧ b ≤ a / 2500 := by
  have haa : a * a ≤ a := by nlinarith
  have he1 : e ≤ 1 / 1000000 := by nlinarith
  have hb1 : b ≤ a / 2500 := by
    by_contra hn
    have hpos : 0 < a * (b - a / 2500) := mul_pos ha (sub_pos.mpr (lt_of_not_ge hn))
    nlinarith
  exact ⟨he1, hb1⟩

theorem transport_margins (a e b : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hsmall : 1000000 * e ≤ a * a) (hb : a * b = 400 * e) :
    32 * e ≤ a ∧ b + 7 * e ≤ a ∧
    (1 / 2 - 6 * e - b > 3 * (1 / 4 + e) / 2) ∧
    (1 / 4 - 7 * e - b ≥ 1 / 5) ∧
    (1 / 4 - 3 * e - 17 * a / 100 > 0) ∧
    (1 / 4 - 11 * e - b > 0) := by
  obtain ⟨he1, hb1⟩ := parameter_bounds a e b ha ha1 hsmall hb
  have haa : a * a ≤ a := by nlinarith
  have he2 : 1000000 * e ≤ a := hsmall.trans haa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem opposite_degree_margin (e : ℝ) (he1 : e ≤ 1 / 1000000) :
    (1 / 2 - 2 * e) * (1 / 4 - 3 * e) / 2 ≥ 1 / 20 := by
  nlinarith [sq_nonneg e]

/-- Two adjacent vertices in a triangle-free induced subgraph have disjoint
neighborhoods. A lower bound at one endpoint bounds the other's degree. -/
theorem triangle_free_neighbor_upper {V : Type*} (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) {u v : V} (hu : u ∈ S) (hv : v ∈ S)
    (huv : G.Adj u v)
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (q : ℕ) (hdeg : S.card ≤ (S.filter (G.Adj v)).card + q) :
    (S.filter (G.Adj u)).card ≤ q := by
  classical
  have hd : Disjoint (S.filter (G.Adj u)) (S.filter (G.Adj v)) := by
    rw [disjoint_left]
    intro w huw hvw
    exact htri u hu v hv w (mem_filter.mp huw).1 huv
      (mem_filter.mp huw).2 (mem_filter.mp hvw).2
  have hsub : S.filter (G.Adj u) ∪ S.filter (G.Adj v) ⊆ S := by
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · exact (mem_filter.mp hw).1
    · exact (mem_filter.mp hw).1
  have hc := card_le_card hsub
  rw [card_union_of_disjoint hd] at hc
  omega

/-- Cost after the robust parity filling and transport, assuming their bounds. -/
theorem robust_certificate_budget (m t h k : ℕ)
    (ht : t ≤ 29 * m) (hh : h ≤ 44 * m) (hk : 3 * k ≤ h) :
    t + 120 * h + 2 * k ≤ 5400 * m := by
  omega

end PartitionedTriangleAbsorption.RobustTransportMarginsStage258
