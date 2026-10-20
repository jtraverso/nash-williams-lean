/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootQueryReserveStage59

/-! # Edge-sampled reserves for a prescribed family of two-root queries

All pairs use one sampled edge set. `H` specifies the bases whose common
neighbours in `U` must survive. The graph may be just the available spokes.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PairReserveStage116

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks

variable {V : Type*} [Fintype V] [DecidableEq V]

def neighbours (U : Finset V) (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) : Finset V := U.filter (fun z => G.Adj x z ∧ G.Adj y z)

theorem neighbours_binary (U : Finset V) (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) :
    neighbours U G x y = RootQueryReserveStage59.neighbours
      (fun v => if v ∈ U then (0 : Fin 2) else 1) G {x, y} 0 := by
  ext z
  simp [neighbours, RootQueryReserveStage59.neighbours]

theorem exists_reserve (U : Finset V) (H : Finset (Sym2 V))
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hrich : ∀ x y, s(x, y) ∈ H → β * Fintype.card V ≤ (neighbours U G x y).card)
    (hbudget : (Fintype.card V : ℝ) * Real.exp (-2 * ρ ^ 2 * Fintype.card V) +
      (Fintype.card V : ℝ) ^ 2 *
        Real.exp (-(ρ ^ 2) ^ 2 * β * Fintype.card V / 2) < 1) :
    ∃ R : Finset (Sym2 V), R ⊆ G.edgeFinset ∧
      DegBounded R (2 * ρ * Fintype.card V) ∧
      ∀ x y, s(x, y) ∈ H → β * ρ ^ 2 / 2 * Fintype.card V ≤
        (neighbours U (ReserveCoverDown.reserveGraph R) x y).card := by
  classical
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := Sym2 V) ρ hρ.le hρ1
  let : IsProbabilityMeasure μ := hμ
  let bad : V ⊕ (V × V) → Set (Sym2 V → Bool)
    | Sum.inl v => {ω | 2 * ρ * Fintype.card V ≤
        (((sampledEdges G ω).filter (fun e => v ∈ e)).card : ℝ)}
    | Sum.inr (x, y) => if s(x, y) ∈ H then
        {ω | ((neighbours U (ReserveCoverDown.reserveGraph (sampledEdges G ω)) x y).card
          : ℝ) ≤ β * ρ ^ 2 / 2 * Fintype.card V} else ∅
  let bound : V ⊕ (V × V) → ℝ
    | Sum.inl _ => Real.exp (-2 * ρ ^ 2 * Fintype.card V)
    | Sum.inr _ => Real.exp (-(ρ ^ 2) ^ 2 * β * Fintype.card V / 2)
  have htail : ∀ i, μ.real (bad i) ≤ bound i := by
    intro i
    cases i with
    | inl v =>
      simpa only [bad, bound, neg_mul] using
        PhysicalStarTail.sampled_star_degree_tail μ hind ρ hρ hmarg G v
    | inr j =>
      obtain ⟨x, y⟩ := j
      by_cases he : s(x, y) ∈ H
      · have ht := RootQueryReserveStage59.root_query_lower_tail
          (fun v => if v ∈ U then (0 : Fin 2) else 1) G {x, y} 0 2
          (by simpa using card_insert_le x ({y} : Finset V)) β ρ hβ hρ hρ1 hn
          (by simpa only [← neighbours_binary] using hrich x y he) μ hind hmarg
        simpa only [bad, bound, ite_eq_left he, ← neighbours_binary] using ht
      · simp only [bad, bound, ite_eq_right he, measureReal_empty]
        exact (Real.exp_pos _).le
  have hsum : ∑ i, bound i < 1 := by
    simpa only [Fintype.sum_sum_type, bound, sum_const, card_univ,
      Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, pow_two] using hbudget
  obtain ⟨ω, hω⟩ := PhysicalReserveTails.exists_simultaneous_outcome μ bad bound htail hsum
  refine ⟨sampledEdges G ω, sampledEdges_subset G ω, ?_, ?_⟩
  · intro v
    exact (not_le.mp (hω (Sum.inl v))).le
  · intro x y he
    have hh := hω (Sum.inr (x, y))
    simp only [bad, ite_eq_left he, Set.mem_ofPred_eq] at hh
    exact (not_le.mp hh).le

end PartitionedTriangleAbsorption.PairReserveStage116
