/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FiniteBernoulliUpperTail

/-! # Reserve queries under one supplied physical-edge probability measure

The measure is fixed before the roots and type are chosen. Thus the query
tails can be combined by a union bound without making incompatible choices
of probability spaces or assuming that different queries are independent.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalReserveTails

open Finset MeasureTheory ProbabilityTheory
open BernoulliBlocks AntiEdgeSelection

theorem commonNeighbour_trials_fixed {V : Type*} [DecidableEq V]
    {t : ℕ} (μ : Measure (Sym2 V → Bool))
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (prob : ℝ) (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal prob)
    (G : SimpleGraph V) (p : V → Fin t) (u v : V) (huv : u ≠ v) (k : Fin t) :
    let W := {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}
    let A := fun w : W => blockEvent (fun e => {ω | ω e = true}) (pathEdges u v w.val)
    iIndepSet A μ ∧ ∀ w, μ (A w) = (ENNReal.ofReal prob) ^ 2 := by
  classical
  let W := {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}
  have hdis : Pairwise (fun a b : W => Disjoint (pathEdges u v a.val)
      (pathEdges u v b.val)) := by
    intro a b hab
    exact SparseReserveGeometry.pathEdges_disjoint u v a.val b.val
      (fun h => hab (Subtype.ext h)) a.property.1.ne.symm a.property.2.1.ne
  constructor
  · exact independent_blocks _ μ
      (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) hind _ hdis
  · intro w
    rw [block_probability _ μ hind _ hmarg, pathEdges_card u v w.val huv]

theorem commonNeighbour_lower_tail {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (μ : Measure (Sym2 V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (prob : ℝ) (hp : 0 ≤ prob)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal prob)
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t)
    (u v : V) (huv : u ≠ v) (k : Fin t)
    (hne : Nonempty {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}) :
    let W := {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}
    let A := fun w : W => blockEvent (fun e => {ω | ω e = true}) (pathEdges u v w.val)
    μ.real {ω | (∑ w : W, (A w).indicator (fun _ => (1 : ℝ)) ω) ≤
      prob ^ 2 * Fintype.card W / 2} ≤
        Real.exp (-prob ^ 4 * Fintype.card W / 2) := by
  classical
  let W := {w : V // G.Adj u w ∧ G.Adj w v ∧ p w = k}
  let A := fun w : W => blockEvent (fun e => {ω : Sym2 V → Bool | ω e = true})
    (pathEdges u v w.val)
  have : Nonempty W := hne
  obtain ⟨hblocks, hprob⟩ := commonNeighbour_trials_fixed μ hind prob hmarg G p u v huv k
  have hreal : ∀ w : W, μ.real (A w) = prob ^ 2 := by
    intro w
    have hpw : μ (A w) = (ENNReal.ofReal prob) ^ 2 := hprob w
    rw [measureReal_def, hpw, ENNReal.toReal_pow, ENNReal.toReal_ofReal hp]
  have hb := FiniteBernoulliTail.lower_half_mean μ A
    (fun w => blockEvent_measurable _
      (fun e => (measurable_pi_apply e) (measurableSet_singleton true)) _) hblocks
    (prob ^ 2) (sq_nonneg prob) hreal
  simpa only [W, A, show (prob ^ 2) ^ 2 = prob ^ 4 by ring] using hb

theorem exists_simultaneous_outcome {I Ω : Type*} [Fintype I] [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (bad : I → Set Ω)
    (bound : I → ℝ) (htail : ∀ i, μ.real (bad i) ≤ bound i)
    (hbudget : ∑ i, bound i < 1) :
    ∃ ω, ∀ i, ω ∉ bad i := by
  have hunion : μ.real (⋃ i, bad i) < 1 :=
    (measureReal_iUnion_fintype_le bad).trans_lt
      ((sum_le_sum fun i _ => htail i).trans_lt hbudget)
  by_contra h
  have hfull : (⋃ i, bad i) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    have hall : ∀ ω, ∃ i, ω ∈ bad i := by
      simpa only [not_exists, not_forall, not_not] using h
    exact hall ω
  simp only [hfull, measureReal_def, measure_univ, ENNReal.toReal_one] at hunion
  exact (lt_irrefl (1 : ℝ)) hunion

end PartitionedTriangleAbsorption.PhysicalReserveTails
