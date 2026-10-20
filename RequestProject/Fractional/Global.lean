/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.Fractional.Key

@[expose] public section

/-!
# Global double counting: Conjecture 4.8 (and hence 4.5) for good weightings
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

lemma negPart_le_sum_trans (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree)
    (hφ : GoodWeighting G φ) (u v : V) :
    negPart G φ u v ≤ ∑ w, (trans G φ u w v + trans G φ v w u) := by
  unfold negPart
  split_ifs with h
  · exact neg_le_sum_trans G φ hδ hφ h.1 h.2
  · exact sum_nonneg fun w _ => add_nonneg (trans_nonneg G φ _ _ _) (trans_nonneg G φ _ _ _)

/-- The fractional Nash-Williams bound for nonzero untied weightings (Conjecture 4.8). -/
theorem good_sum_nonneg (hδ : 3 * Fintype.card V ≤ 4 * G.minDegree)
    (hφ : GoodWeighting G φ) :
    0 ≤ ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0) := by
  have hT : ∑ u, ∑ v, ∑ w, (trans G φ u w v + trans G φ v w u) =
      ∑ a, ∑ b, ∑ x, (trans G φ a b x + trans G φ b a x) := by
    simp only [sum_add_distrib]
    congr 1
    · rw [sum_congr rfl fun u _ => sum_comm]
    · rw [sum_comm]
      rw [sum_congr rfl fun u _ => sum_comm]
      exact sum_comm
  have h1 : ∑ u, ∑ v, negPart G φ u v ≤ ∑ u, ∑ v, ∑ w, (trans G φ u w v + trans G φ v w u) :=
    sum_le_sum fun u _ => sum_le_sum fun v _ => negPart_le_sum_trans G φ hδ hφ u v
  have h2 : ∑ a, ∑ b, ∑ x, (trans G φ a b x + trans G φ b a x) ≤ ∑ a, ∑ b, posPart G φ a b :=
    sum_le_sum fun a _ => sum_le_sum fun b _ => sum_trans_le_pos G φ a b
  have h3 : ∑ a, ∑ b, (if G.Adj a b then φ s(a, b) else 0) =
      ∑ a, ∑ b, posPart G φ a b - ∑ a, ∑ b, negPart G φ a b := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun b _ => ?_
    unfold posPart negPart
    by_cases hab : G.Adj a b
    · rcases (hφ.nz s(a, b)).lt_or_gt with h | h
      · simp [hab, h, not_lt.2 h.le]
      · simp [hab, h, not_lt.2 h.le]
    · simp [hab]
  rw [h3]; linarith

end NashWilliams.Frac
