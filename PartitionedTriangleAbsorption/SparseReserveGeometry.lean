/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveCoverDown

/-! # Physical independence blocks and deterministic survival for a sparse reserve

For a fixed pair of distinct roots, different common neighbours use disjoint
two-edge blocks. Removing an edge set of maximum degree `d` loses at most `2d`
common neighbours. Neither result asserts existence of a random reserve.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SparseReserveGeometry

open Finset AntiEdgeSelection ReserveCoverDown

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

omit [Fintype V] in
/-- Shared vertices are allowed; shared physical edges are not. -/
theorem pathEdges_disjoint (u v a b : V) (hab : a ≠ b)
    (hau : a ≠ u) (hav : a ≠ v) :
    Disjoint (pathEdges u v a) (pathEdges u v b) := by
  apply disjoint_left.mpr
  intro e hea heb
  simp only [pathEdges, mem_insert, mem_singleton] at hea heb
  rcases hea with rfl | rfl <;> rcases heb with h | h
  all_goals
    rcases Sym2.eq_iff.mp h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact hab h₂
    · first | exact hau h₂ | exact hav h₂

/-- Actual common-neighbour candidates provide the disjoint blocks needed for
independent Bernoulli trials, even when the roots lie in the same part. -/
theorem commonNeighbour_blocks_disjoint (G : SimpleGraph V)
    [DecidableRel G.Adj] (p : V → Fin t) (u v : V) (k : Fin t) :
    (univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k) : Set V).PairwiseDisjoint
      (pathEdges u v) := by
  intro a ha b _ hab
  have ha' := (mem_filter.mp ha).2
  exact pathEdges_disjoint u v a b hab ha'.1.ne.symm ha'.2.1.ne

/-- `G` with the physical edges of `B` removed. -/
abbrev withoutEdges (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) : SimpleGraph V := reserveGraph (G.edgeFinset \ B)

theorem withoutEdges_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (u v : V) :
    (withoutEdges G B).Adj u v ↔ G.Adj u v ∧ s(u, v) ∉ B := by
  rw [SimpleGraph.fromEdgeSet_adj]
  simp only [mem_coe, mem_sdiff, SimpleGraph.mem_edgeFinset]
  constructor
  · exact fun h => h.1
  · intro h
    exact ⟨h, h.1.ne⟩

/-- Quantitative survival, including the boundary case of equality. -/
theorem antiEdgeful_withoutEdges (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (α β d : ℝ)
    (hanti : AntiEdgeful p F G α) (hB : DegBounded B d)
    (hbudget : β * Fintype.card V + 2 * d ≤ α * Fintype.card V) :
    AntiEdgeful p F (withoutEdges G B) β := by
  classical
  intro τ hτ i j k heq u v huv hu hv
  let W := univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k)
  let good := W \ (blockedNeighbours B u ∪ blockedNeighbours B v)
  have hcount := available_card_budget W ∅ B u v
  simp only [empty_union, card_empty, Nat.add_zero] at hcount
  have hcountR : (W.card : ℝ) ≤ (good.card : ℝ) + incidentLoad B u +
      incidentLoad B v := by exact_mod_cast hcount
  have hlarge : α * Fintype.card V ≤ (W.card : ℝ) :=
    hanti τ hτ i j k heq u v huv hu hv
  have hBu : (incidentLoad B u : ℝ) ≤ d := hB u
  have hBv : (incidentLoad B v : ℝ) ≤ d := hB v
  have hgood : good = univ.filter (fun w => (withoutEdges G B).Adj u w ∧
      (withoutEdges G B).Adj w v ∧ p w = k) := by
    ext w
    simp only [good, W, mem_sdiff, mem_filter, mem_univ, true_and,
      mem_union, blockedNeighbours, not_or, withoutEdges_adj]
    simp only [Sym2.eq_swap (a := w) (b := v)]
    tauto
  rw [← hgood]
  linarith

/-- The feedback's reserve bound `Δ(B) ≤ 2pn` preserves half the original
typed anti-edge supply whenever `p ≤ α/8`. -/
theorem antiEdgeful_without_sparseReserve (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (α prob : ℝ)
    (hanti : AntiEdgeful p F G α)
    (hB : DegBounded B (2 * prob * Fintype.card V)) (hprob : prob ≤ α / 8) :
    AntiEdgeful p F (withoutEdges G B) (α / 2) := by
  apply antiEdgeful_withoutEdges p F G B α (α / 2)
    (2 * prob * Fintype.card V) hanti hB
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  nlinarith

end PartitionedTriangleAbsorption.SparseReserveGeometry
