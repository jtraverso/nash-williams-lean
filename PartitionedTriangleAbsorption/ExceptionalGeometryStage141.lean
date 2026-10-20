/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CleanupGeometryStage140
public import PartitionedTriangleAbsorption.TypedCoverDownConsumer

/-! # Average internal error and the exceptional set

These estimates are derived from the graph and its partition, not from a
supplied cleanup packing. They do not assert that the exceptional vertices
have been removed or that the remaining cut balances have been preserved.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ExceptionalGeometryStage141

open Finset AntiEdgeSelection MatchedQuotaStage140 CleanupSupplyStage140
open ClassRepresentativesStage65 FourClassSeedStage80

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem total_internal_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) :
    ∑ v : V, (internalNeighbours G p v).card = 2 * (internal p G.edgeFinset).card := by
  simp_rw [← CleanupGeometryStage140.internal_load_eq G p]
  exact TypedCoverDown.sum_degrees_eq_two_mul_card _
    (fun e he => G.not_isDiag_of_mem_edgeFinset (mem_filter.mp he).1)

omit [DecidableEq V] in
theorem class_average_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v) (i : Fin 4) :
    (classSet p i).card * ((classSet p i).card - (Fintype.card V : ℝ) / 4) ≤
      2 * (internal p G.edgeFinset).card := by
  classical
  have hv : ∀ v ∈ classSet p i,
      ((classSet p i).card : ℝ) - Fintype.card V / 4 ≤ (internalNeighbours G p v).card := by
    intro v hv
    have hp := (mem_filter.mp hv).2
    have ha : ((missingOutside G p v).card : ℝ) + G.degree v +
        (classSet p (p v)).card = Fintype.card V + (internalNeighbours G p v).card :=
      by exact_mod_cast degree_class_account G p v
    rw [hp] at ha
    nlinarith [hdeg v, (show (0 : ℝ) ≤ (missingOutside G p v).card from Nat.cast_nonneg _)]
  calc
    _ = ∑ _v ∈ classSet p i, (((classSet p i).card : ℝ) - Fintype.card V / 4) := by
      simp [mul_sub]
    _ ≤ ∑ v ∈ classSet p i, ((internalNeighbours G p v).card : ℝ) := sum_le_sum hv
    _ ≤ ∑ v : V, ((internalNeighbours G p v).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = 2 * (internal p G.edgeFinset).card := by
      exact_mod_cast total_internal_degree G p

omit [DecidableEq V] in
theorem class_upper_average (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho : ℝ) (hrho : 0 ≤ rho) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (i : Fin 4) :
    ((classSet p i).card : ℝ) ≤ (1 / 4 + 8 * rho) * Fintype.card V := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hb := class_average_budget G p hdeg i
  by_cases hi : ((classSet p i).card : ℝ) ≤ Fintype.card V / 4
  · nlinarith
  · have hexcess : 0 ≤ ((classSet p i).card : ℝ) - Fintype.card V / 4 := by linarith
    have hm := mul_le_mul_of_nonneg_right (le_of_lt (lt_of_not_ge hi)) hexcess
    have hh : (Fintype.card V : ℝ) *
        (((classSet p i).card : ℝ) - Fintype.card V / 4) ≤
        (Fintype.card V : ℝ) * (8 * rho * Fintype.card V) := by nlinarith
    have hd := (mul_le_mul_iff_right₀ hnR).mp hh
    linarith

omit [DecidableEq V] in
theorem class_lower_average (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho : ℝ) (hrho : 0 ≤ rho) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (i : Fin 4) :
    (1 / 4 - 24 * rho) * Fintype.card V ≤ ((classSet p i).card : ℝ) := by
  have h0 := class_upper_average G p rho hrho hn hdeg herr 0
  have h1 := class_upper_average G p rho hrho hn hdeg herr 1
  have h2 := class_upper_average G p rho hrho hn hdeg herr 2
  have h3 := class_upper_average G p rho hrho hn hdeg herr 3
  have ht : ∑ j : Fin 4, ((classSet p j).card : ℝ) = Fintype.card V :=
    by exact_mod_cast sum_class_card p
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero] at ht
  change (classSet p 0).card + ((classSet p 1).card +
    ((classSet p 2).card + ((classSet p 3).card + (0 : ℝ)))) = Fintype.card V at ht
  fin_cases i
  · change (1 / 4 - 24 * rho) * Fintype.card V ≤ ((classSet p 0).card : ℝ)
    nlinarith
  · change (1 / 4 - 24 * rho) * Fintype.card V ≤ ((classSet p 1).card : ℝ)
    nlinarith
  · change (1 / 4 - 24 * rho) * Fintype.card V ≤ ((classSet p 2).card : ℝ)
    nlinarith
  · change (1 / 4 - 24 * rho) * Fintype.card V ≤ ((classSet p 3).card : ℝ)
    nlinarith

noncomputable def exceptional (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (tau : ℝ) : Finset V :=
  univ.filter (fun v => tau * Fintype.card V < ((internalNeighbours G p v).card : ℝ))

theorem outside_internal_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (tau : ℝ) (v : V) (hv : v ∉ exceptional G p tau) :
    ((internalNeighbours G p v).card : ℝ) ≤ tau * Fintype.card V := by
  classical
  simpa only [exceptional, mem_filter, mem_univ, true_and, not_lt] using hv

theorem exceptional_card_budget (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (tau : ℝ) :
    tau * Fintype.card V * (exceptional G p tau).card ≤
      2 * (internal p G.edgeFinset).card := by
  classical
  calc
    _ = ∑ _v ∈ exceptional G p tau, tau * Fintype.card V := by simp [mul_comm]
    _ ≤ ∑ v ∈ exceptional G p tau, ((internalNeighbours G p v).card : ℝ) := by
      apply sum_le_sum
      intro v hv
      exact le_of_lt (mem_filter.mp hv).2
    _ ≤ ∑ v : V, ((internalNeighbours G p v).card : ℝ) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => Nat.cast_nonneg _)
    _ = 2 * (internal p G.edgeFinset).card := by
      exact_mod_cast total_internal_degree G p

theorem exceptional_card_average (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hn : 0 < Fintype.card V)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2) :
    tau * (exceptional G p tau).card ≤ 2 * rho * Fintype.card V := by
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hb := exceptional_card_budget G p tau
  have hh : (Fintype.card V : ℝ) * (tau * (exceptional G p tau).card) ≤
      (Fintype.card V : ℝ) * (2 * rho * Fintype.card V) := by nlinarith
  exact (mul_le_mul_iff_right₀ hnR).mp hh

theorem typical_missing_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hrho : 0 ≤ rho) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (v : V) (hv : v ∉ exceptional G p tau) :
    ((missingOutside G p v).card : ℝ) ≤ (24 * rho + tau) * Fintype.card V := by
  have ha : ((missingOutside G p v).card : ℝ) + G.degree v +
      (classSet p (p v)).card = Fintype.card V + (internalNeighbours G p v).card :=
    by exact_mod_cast degree_class_account G p v
  have hl := class_lower_average G p rho hrho hn hdeg herr (p v)
  have hi := outside_internal_bound G p tau v hv
  nlinarith [hdeg v]

theorem typical_candidates_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hrho : 0 ≤ rho) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (u v : V) (hu : u ∉ exceptional G p tau) (hv : v ∉ exceptional G p tau)
    (j : Fin 4) (hju : j ≠ p u) (hjv : j ≠ p v) :
    (1 / 4 - 72 * rho - 2 * tau) * Fintype.card V ≤
      ((candidates G p u v j).card : ℝ) := by
  have hb : ((classSet p j).card : ℝ) ≤ (candidates G p u v j).card +
      (missingOutside G p u).card + (missingOutside G p v).card :=
    by exact_mod_cast candidates_budget G p u v j hju hjv
  have hl := class_lower_average G p rho hrho hn hdeg herr j
  have hu' := typical_missing_bound G p rho tau hrho hn hdeg herr u hu
  have hv' := typical_missing_bound G p rho tau hrho hn hdeg herr v hv
  nlinarith

theorem typical_candidates_outside_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : V → Fin 4) (rho tau : ℝ) (hrho : 0 ≤ rho) (hn : 0 < Fintype.card V)
    (hdeg : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (u v : V) (hu : u ∉ exceptional G p tau) (hv : v ∉ exceptional G p tau)
    (j : Fin 4) (hju : j ≠ p u) (hjv : j ≠ p v) :
    (1 / 4 - 72 * rho - 2 * tau) * Fintype.card V - (exceptional G p tau).card ≤
      ((candidates G p u v j \ exceptional G p tau).card : ℝ) := by
  classical
  have hh := typical_candidates_lower G p rho tau hrho hn hdeg herr u v hu hv j hju hjv
  have hd := card_sdiff_add_card_inter (candidates G p u v j) (exceptional G p tau)
  have hi := card_le_card (inter_subset_right :
    candidates G p u v j ∩ exceptional G p tau ⊆ exceptional G p tau)
  have hc : (candidates G p u v j).card ≤
      (candidates G p u v j \ exceptional G p tau).card + (exceptional G p tau).card := by
    omega
  have hcR : ((candidates G p u v j).card : ℝ) ≤
      (candidates G p u v j \ exceptional G p tau).card + (exceptional G p tau).card :=
    by exact_mod_cast hc
  linarith

end PartitionedTriangleAbsorption.ExceptionalGeometryStage141
