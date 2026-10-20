/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.GoodRootEdgeStage261
public import PartitionedTriangleAbsorption.OppositeEdgeTransportStage259

/-! Any two edges inside the good remainder have a common opposite edge.
The two physical K4s are produced from the missing-neighbor estimates. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open Finset OppositeEdgeTransportStage259

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The opposite-edge distance between two good-remainder edges is at most
two. No triangle or connectivity assumption on that remainder is required. -/
theorem good_edges_have_common_opposite (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + e) * Fintype.card V)
    (u v p q r t : V) (hpq : G.Adj p q) (hrt : G.Adj r t) :
    let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
    let B := univ.filter (fun x => x ∉ S ∧ a * Fintype.card V / 100 <
      ((S.filter (fun y => ¬ G.Adj x y)).card : ℝ))
    let R := univ \ (S ∪ B)
    p ∈ R → q ∈ R → r ∈ R → t ∈ R →
      ∃ f : G.edgeSet,
        (oppositeEdgeGraph G).Adj (edge G hpq) f ∧
        (oppositeEdgeGraph G).Adj f (edge G hrt) := by
  classical
  intro S B R hp hq hr ht
  have hcard : ({p, q, r, t} : Finset V).card ≤ 17 := by
    have h1 := card_insert_le p ({q, r, t} : Finset V)
    have h2 := card_insert_le q ({r, t} : Finset V)
    have h3 := card_insert_le r ({t} : Finset V)
    simp only [card_singleton] at h3
    omega
  have hgood : ({p, q, r, t} : Finset V) ⊆ R := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  obtain ⟨x, _, y, _, _, hxy, hall⟩ :=
    good_roots_have_common_edge G a e ha ha1 he hn hsmall hdeg u v u
      {p, q, r, t} hcard hgood
  have hpx := hall p (by simp)
  have hqx := hall q (by simp)
  have hrx := hall r (by simp)
  have htx := hall t (by simp)
  exact ⟨edge G hxy,
    opposite_adj G hpq hxy hpx.1.symm hpx.2.symm hqx.1.symm hqx.2.symm,
    opposite_adj G hxy hrt hrx.1 htx.1 hrx.2 htx.2⟩

end PartitionedTriangleAbsorption.GoodRemaindersStage261
