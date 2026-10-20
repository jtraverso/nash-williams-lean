/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BoundedCoreReserveStage103
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! # A uniformly sparse absorber for a bounded terminal core

The order threshold precedes G, X and the future residual. This is the terminal
core interface for a vortex, not a construction of that vortex.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BoundedCoreStage104

open Finset TypedTransformer PairMoveSelectionStage85 AntiEdgeSelection

variable {t : ℕ}

/-- A genuine uniform terminal-core absorber, with its degree bound and its
universal residual quantifier. No private family or fixed reserve is an input. -/
theorem exists_uniform_terminal_absorber (F : Finset (Multiset (Fin t)))
    (hcard : ∀ τ ∈ F, τ.card = 3) (hF : ThreeStepLinks F) (K : ℕ)
    (gamma eta : ℝ) (hg : 0 < gamma) (he : 0 < eta) :
    ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin t),
      N ≤ Fintype.card V →
      CompatibleSupply p F G (gamma * Fintype.card V) →
      ∀ B X : Finset (Sym2 V),
      DegBounded B (gamma * Fintype.card V / 5) →
      X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
      ∃ C, C ⊆ G.edgeFinset ∧ Disjoint C (B ∪ X) ∧ HasDecomp p F C ∧
        DegBounded C (eta * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (C ∪ L) := by
  obtain ⟨q, prod⟩ := BoundedCoreStage103.exists_fixed_absorber F hcard hF K
  let M : ℕ := 2 ^ K * (93 * K + 282 * q)
  let T : ℝ := 388 * K + 1164 * q + 4 * (K + (M : ℝ))
  obtain ⟨N, hN⟩ := exists_nat_gt (max (5 * T / gamma) ((M : ℝ) / eta))
  refine ⟨N, fun {V} _ _ G _ p hn hs B X hB hXG hXB hK => ?_⟩
  have hnR : (N : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have ht : 5 * T < gamma * Fintype.card V := by
    have h := (le_max_left (5 * T / gamma) ((M : ℝ) / eta)).trans_lt hN
    have h' := (div_lt_iff₀ hg).mp (h.trans_le hnR)
    simpa only [mul_comm] using h'
  have hm : (M : ℝ) < eta * Fintype.card V := by
    have h := (le_max_right (5 * T / gamma) ((M : ℝ) / eta)).trans_lt hN
    have h' := (div_lt_iff₀ he).mp (h.trans_le hnR)
    simpa only [mul_comm] using h'
  obtain ⟨C, hCG, havoid, hdec, hCc, hall⟩ :=
    prod G p (gamma * Fintype.card V) (gamma * Fintype.card V / 5) hs B X hB
      (by positivity) hXG hXB hK (by
        simp only [T, M, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at ht
        linarith)
  refine ⟨C, hCG, havoid, hdec, ?_, hall⟩
  intro v
  have hc : (C.card : ℝ) ≤ M := by exact_mod_cast hCc
  have hl : (incidentLoad C v : ℝ) ≤ C.card := by
    exact_mod_cast card_le_card (filter_subset (fun e => v ∈ e) C)
  exact (hl.trans hc).trans hm.le

end PartitionedTriangleAbsorption.BoundedCoreStage104
