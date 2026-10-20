/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1PuncturedWeightsStage217
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Rootwise loss of weighted triangle extensions in the actual damaged graph

For a surviving edge uv, possible third vertices lost on passing from G to H
are charged to missing incidences at u or v. This works for any chosen set of
typed/protected extensions; it does not require the leftover to be typical.
The ideal graph-counting input and reserve construction remain separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1DamagedExtensionsStage218

open Finset

variable {V : Type*} [Fintype V]

theorem lost_extensions_card (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (u v : V) (C : Finset V)
    (hC : ∀ w ∈ C, G.Adj u w ∧ G.Adj v w) :
    (C.filter fun w => ¬ (H.Adj u w ∧ H.Adj v w)).card ≤
      (univ.filter fun w => G.Adj u w ∧ ¬ H.Adj u w).card +
      (univ.filter fun w => G.Adj v w ∧ ¬ H.Adj v w).card := by
  classical
  have hsub : (C.filter fun w => ¬ (H.Adj u w ∧ H.Adj v w)) ⊆
      (univ.filter fun w => G.Adj u w ∧ ¬ H.Adj u w) ∪
      (univ.filter fun w => G.Adj v w ∧ ¬ H.Adj v w) := by
    intro w hw
    obtain ⟨hwC, hbad⟩ := mem_filter.mp hw
    obtain ⟨hu, hv⟩ := hC w hwC
    by_cases hHu : H.Adj u w
    · have hHv : ¬ H.Adj v w := fun hh => hbad ⟨hHu, hh⟩
      exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hv, hHv⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hu, hHu⟩)
  exact (card_le_card hsub).trans (card_union_le _ _)

theorem weighted_extensions_survive (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (u v : V) (C : Finset V) (w : V → ℝ)
    (b d : ℝ) (hb : 0 ≤ b) (hC : ∀ z ∈ C, G.Adj u z ∧ G.Adj v z)
    (hw : ∀ z ∈ C, w z ≤ b)
    (hu : ((univ.filter fun z => G.Adj u z ∧ ¬ H.Adj u z).card : ℝ) ≤ d)
    (hv : ((univ.filter fun z => G.Adj v z ∧ ¬ H.Adj v z).card : ℝ) ≤ d) :
    (∑ z ∈ C, w z) - 2 * d * b ≤
      ∑ z ∈ C.filter (fun z => H.Adj u z ∧ H.Adj v z), w z := by
  classical
  let B := C.filter fun z => ¬ (H.Adj u z ∧ H.Adj v z)
  have hcard : (B.card : ℝ) ≤ 2 * d := by
    have hnat := lost_extensions_card G H u v C hC
    have hr : (B.card : ℝ) ≤
        (univ.filter fun z => G.Adj u z ∧ ¬ H.Adj u z).card +
        (univ.filter fun z => G.Adj v z ∧ ¬ H.Adj v z).card := by
      exact_mod_cast hnat
    linarith
  have hsum : ∑ z ∈ B, w z ≤ (B.card : ℝ) * b := by
    have hh := sum_le_card_nsmul B w b (fun z hz => hw z (mem_filter.mp hz).1)
    simpa [nsmul_eq_mul] using hh
  have hsum' : ∑ z ∈ B, w z ≤ 2 * d * b :=
    hsum.trans (mul_le_mul_of_nonneg_right hcard hb)
  have heq := sum_filter_add_sum_filter_not C (fun z => H.Adj u z ∧ H.Adj v z) w
  change _ + ∑ z ∈ B, w z = _ at heq
  linarith

theorem ideal_load_survives_damage (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] (u v : V) (C : Finset V) (w : V → ℝ)
    (n t d : ℝ) (hn : 0 < n)
    (hC : ∀ z ∈ C, G.Adj u z ∧ G.Adj v z)
    (hw : ∀ z ∈ C, w z ≤ 4 / n)
    (hu : ((univ.filter fun z => G.Adj u z ∧ ¬ H.Adj u z).card : ℝ) ≤ d)
    (hv : ((univ.filter fun z => G.Adj v z ∧ ¬ H.Adj v z).card : ℝ) ≤ d)
    (hload : 1 - 1 / t ≤ ∑ z ∈ C, w z) :
    1 - 1 / t - 8 * d / n ≤
      ∑ z ∈ C.filter (fun z => H.Adj u z ∧ H.Adj v z), w z := by
  classical
  have h := weighted_extensions_survive G H u v C w (4 / n) d
    (by positivity) hC hw hu hv
  have hfactor : 2 * d * (4 / n) = 8 * d / n := by ring
  rw [hfactor] at h
  linarith

end PartitionedTriangleAbsorption.F1DamagedExtensionsStage218
