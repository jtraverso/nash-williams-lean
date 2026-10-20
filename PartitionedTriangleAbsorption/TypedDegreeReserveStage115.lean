/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RootQueryReserveStage59

/-! # A sparse reserve with neighbours in each other label class

This is an edge-sampling producer, not a supplied reserve. The finite tail
budget and the host's typed degree lower bounds remain explicit inputs.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedDegreeReserveStage115

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks

variable {V : Type*} [Fintype V] [DecidableEq V]

def neighbours (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (i : Fin 4) : Finset V :=
  univ.filter (fun v => p v = i ∧ G.Adj u v)

theorem neighbours_binary (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (u : V) (i : Fin 4) :
    neighbours p G u i = RootQueryReserveStage59.neighbours
      (fun v => if p v = i then (0 : Fin 2) else 1) G {u} 0 := by
  ext v
  simp [neighbours, RootQueryReserveStage59.neighbours]

theorem exists_reserve (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hG : ∀ u i, i ≠ p u → β * Fintype.card V ≤ (neighbours p G u i).card)
    (hbudget : (Fintype.card V : ℝ) * Real.exp (-2 * ρ ^ 2 * Fintype.card V) +
      (Fintype.card V * 4 : ℝ) *
        Real.exp (-ρ ^ 2 * β * Fintype.card V / 2) < 1) :
    ∃ R : Finset (Sym2 V), R ⊆ G.edgeFinset ∧
      DegBounded R (2 * ρ * Fintype.card V) ∧
      ∀ u i, i ≠ p u → β * ρ / 2 * Fintype.card V ≤
        (neighbours p (ReserveCoverDown.reserveGraph R) u i).card := by
  classical
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := Sym2 V) ρ hρ.le hρ1
  let : IsProbabilityMeasure μ := hμ
  let bad : V ⊕ (V × Fin 4) → Set (Sym2 V → Bool)
    | Sum.inl v => {ω | 2 * ρ * Fintype.card V ≤
        (((sampledEdges G ω).filter (fun e => v ∈ e)).card : ℝ)}
    | Sum.inr (u, i) => if i = p u then ∅ else
        {ω | ((neighbours p (ReserveCoverDown.reserveGraph (sampledEdges G ω)) u i).card
          : ℝ) ≤ β * ρ / 2 * Fintype.card V}
  let bound : V ⊕ (V × Fin 4) → ℝ
    | Sum.inl _ => Real.exp (-2 * ρ ^ 2 * Fintype.card V)
    | Sum.inr _ => Real.exp (-ρ ^ 2 * β * Fintype.card V / 2)
  have htail : ∀ i, μ.real (bad i) ≤ bound i := by
    intro i
    cases i with
    | inl v =>
      simpa only [bad, bound, neg_mul] using
        PhysicalStarTail.sampled_star_degree_tail μ hind ρ hρ hmarg G v
    | inr j =>
      obtain ⟨u, i⟩ := j
      by_cases hi : i = p u
      · simp only [bad, bound, ite_eq_left hi, measureReal_empty]
        exact (Real.exp_pos _).le
      · have ht := RootQueryReserveStage59.root_query_lower_tail
          (fun v => if p v = i then (0 : Fin 2) else 1) G {u} 0 1
          (by simp) β ρ hβ hρ hρ1 hn
          (by simpa only [← neighbours_binary] using hG u i hi) μ hind hmarg
        simpa only [bad, bound, ite_eq_right hi, ← neighbours_binary, pow_one,
          neg_mul] using ht
  have hsum : ∑ i, bound i < 1 := by
    simpa only [Fintype.sum_sum_type, bound, sum_const, card_univ,
      Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      using hbudget
  obtain ⟨ω, hω⟩ := PhysicalReserveTails.exists_simultaneous_outcome μ bad bound htail hsum
  refine ⟨sampledEdges G ω, sampledEdges_subset G ω, ?_, ?_⟩
  · intro v
    exact (not_le.mp (hω (Sum.inl v))).le
  · intro u i hi
    have h := hω (Sum.inr (u, i))
    simp only [bad, ite_eq_right hi, Set.mem_ofPred_eq] at h
    exact (not_le.mp h).le

end PartitionedTriangleAbsorption.TypedDegreeReserveStage115
