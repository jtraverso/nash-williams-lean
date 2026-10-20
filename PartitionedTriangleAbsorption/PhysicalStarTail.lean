/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FiniteBernoulliUpperTail

/-! # A degree tail for the actual sparse physical reserve

Trials are indexed by distinct incident graph edges, not by triangles. Their
number is at most the number of graph vertices. This concerns the reserve
sampling only, and does not claim concentration for the dependent nibble.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalStarTail

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks

theorem retained_count_eq_sum {E : Type*} (B : Finset E)
    (ω : E → Bool) :
    ((B.filter (fun e => ω e = true)).card : ℝ) =
      ∑ e : B, ({ω : E → Bool | ω e.val = true}).indicator (fun _ => (1 : ℝ)) ω := by
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_coe_sort B (fun e : E => if ω e = true then (1 : ℝ) else 0)]
  exact (Finset.sum_boole _ _).symm

theorem retained_count_upper_tail {E : Type*}
    (μ : Measure (E → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (prob : ℝ) (hp : 0 < prob)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal prob)
    (B : Finset E) (n : ℝ) (hn : 0 < n) (hcard : (B.card : ℝ) ≤ n) :
    μ.real {ω | 2 * prob * n ≤ ((B.filter (fun e => ω e = true)).card : ℝ)} ≤
      Real.exp (-(2 * prob ^ 2 * n)) := by
  classical
  by_cases hempty : B = ∅
  · simp only [hempty, filter_empty, card_empty, Nat.cast_zero]
    have ht : ¬ 2 * prob * n ≤ 0 := not_le.mpr (by positivity)
    simp only [ht, Set.ofPred_false, measureReal_empty]
    exact (Real.exp_pos _).le
  have : Nonempty B := (Finset.nonempty_iff_ne_empty.mpr hempty).to_subtype
  let A : B → Set (E → Bool) := fun e => {ω | ω e.val = true}
  have hb := FiniteBernoulliUpperTail.upper_deviation μ A
    (fun e => show MeasurableSet {ω : E → Bool | ω e.val = true} from
      (measurable_pi_apply e.val : Measurable (fun ω : E → Bool => ω e.val))
        (measurableSet_singleton true))
    (hind.precomp Subtype.val_injective) prob (prob * n) (by positivity)
    (fun e => by simp [A, measureReal_def, hmarg, ENNReal.toReal_ofReal hp.le])
  have hsub : {ω | 2 * prob * n ≤ ((B.filter (fun e => ω e = true)).card : ℝ)} ⊆
      {ω | prob * Fintype.card B + prob * n ≤
        ∑ e : B, (A e).indicator (fun _ => (1 : ℝ)) ω} := by
    intro ω hω
    change 2 * prob * n ≤ _ at hω
    rw [retained_count_eq_sum] at hω
    change prob * Fintype.card B + prob * n ≤ _
    have hc : (Fintype.card B : ℝ) ≤ n := by simpa using hcard
    have := mul_le_mul_of_nonneg_left hc hp.le
    dsimp only [A] at hω ⊢
    linarith
  have hm : 0 < (Fintype.card B : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card B : ℝ) ≤ n := by simpa using hcard
  have he : -2 * (prob * n) ^ 2 / Fintype.card B ≤ -(2 * prob ^ 2 * n) := by
    apply (div_le_iff₀ hm).mpr
    nlinarith [mul_le_mul_of_nonneg_left hc (show 0 ≤ 2 * prob ^ 2 * n by positivity)]
  exact (measureReal_mono hsub).trans (hb.trans (Real.exp_le_exp.mpr he))

theorem sampled_star_degree_tail {V : Type*} [Fintype V] [DecidableEq V]
    (μ : Measure (Sym2 V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun e => {ω | ω e = true}) μ)
    (prob : ℝ) (hp : 0 < prob)
    (hmarg : ∀ e, μ {ω | ω e = true} = ENNReal.ofReal prob)
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    μ.real {ω | 2 * prob * Fintype.card V ≤
        (((sampledEdges G ω).filter (fun e => v ∈ e)).card : ℝ)} ≤
      Real.exp (-(2 * prob ^ 2 * Fintype.card V)) := by
  have hn : 0 < (Fintype.card V : ℝ) := by
    have : Nonempty V := ⟨v⟩
    exact_mod_cast Fintype.card_pos
  have hstar : ∀ ω, (sampledEdges G ω).filter (fun e => v ∈ e) =
      (G.incidenceFinset v).filter (fun e => ω e = true) := by
    intro ω
    rw [SimpleGraph.incidenceFinset_eq_filter]
    ext e
    simp only [sampledEdges, mem_filter]
    tauto
  simp_rw [hstar]
  exact retained_count_upper_tail μ hind prob hp hmarg _ _ hn
    (by rw [SimpleGraph.card_incidenceFinset_eq_degree]
        exact_mod_cast (G.degree_lt_card_verts v).le)

end PartitionedTriangleAbsorption.PhysicalStarTail
