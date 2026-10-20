/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Stage205Adapter
import PartitionedTriangleAbsorption.UniformBoundedCoreStage104

/-!
# Theorem 14.7 for `F₁`: a terminal omni-absorber for bounded cores (produced)

This file checks the root and resource budgets of the ported generic producer
`PartitionedTriangleAbsorption.BoundedCoreStage104.exists_uniform_terminal_absorber` on the
idealized `F₁`-hosts of `Theorem147F1Statement`, and applies it.

* **Root budget.**  The producer needs `CompatibleSupply p F1 G (γ n)`: every set `S` of at most
  **four** roots and every class `i` such that each root's class is `F₁`-linked to `i` has at
  least `γ n` common neighbours in `V_i`.  On an idealized `F₁`-host with `ε ≤ 1/100` this holds
  with `γ = 1/8` (`compatibleSupply_F1_of_idealized`): each root misses at most `ε n` vertices of
  an allowed class, so at least `(1-ε)n/4 - 4εn ≥ n/8` common neighbours remain.  This is a real
  four-root count from the third clause of `IsIdealizedT`, not two-root anti-edgefulness.
* **Typed compatibility.**  `ThreeStepLinks F1` is the ported `TypedTransformer.F1_three_step`
  (a finite check).
* **Resource budget.**  Forbidden edges `B` with `Δ(B) ≤ n/40` (`= γ n/5`), core `X` with
  `|X| ≤ K`; output degree `≤ η n` once `n ≥ N(K, η)`.

**What this is and is not.**  `F1_ideal_terminal_absorber` is a *producer*: one physical
absorber `C`, built before the leftover, with `C ∪ L` decomposable for **every** integrally
divisible `L ⊆ X`.  It only handles a core of **bounded** size `K`.  It does not repair the
quadratic residual `J` of `F1_ideal_reserve_confinement`; reducing the leftover to a bounded core
(a vortex / iterated cover-down on `F₁`-hosts) is not proved here.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

/-- Four-root compatible supply on an idealized `F₁`-host. -/
theorem compatibleSupply_F1_of_idealized {V : Type} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1 / 100) (hid : IsIdealizedT F1 ε G p) :
    PairMoveSelectionStage85.CompatibleSupply p F1 G (1 / 8 * Fintype.card V) := by
  classical
  intro S hS i hi
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  -- non-neighbours of each root in `V_i`
  let miss : V → Finset V := fun u => univ.filter fun y => p y = i ∧ ¬ G.Adj u y
  have hmiss : ∀ u ∈ S, ((miss u).card : ℝ) ≤ ε * n := by
    intro u hu
    obtain ⟨k, hk⟩ := hi u hu
    have hal : AllowedT F1 (p u) i := by
      refine ⟨k, ?_⟩
      have : ({p u, i, k} : Multiset (Fin 4)) = {i, p u, k} := triple_swap12 _ _ _
      rw [this]; exact hk
    have h1 := hid.2.2 u i hal
    have h2 := card_nonNbr_add_degT G p u i
    have h2' : ((miss u).card : ℝ) + (degT G p u i : ℝ) = ((clsT p i).card : ℝ) := by
      exact_mod_cast h2
    linarith
  have hsub : clsT p i ⊆ PartitionedTriangleAbsorption.TypedEmbeddingSelection.typedNeighbours
      p G S i ∪ S.biUnion miss := by
    intro w hw
    have hpw : p w = i := (mem_filter.mp hw).2
    by_cases hall : ∀ u ∈ S, G.Adj u w
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hpw, hall⟩)
    · push_neg at hall
      obtain ⟨u, hu, hnot⟩ := hall
      exact mem_union_right _ (mem_biUnion.mpr ⟨u, hu, mem_filter.mpr ⟨mem_univ _, hpw, hnot⟩⟩)
  have hc1 := (card_le_card hsub).trans (card_union_le _ _)
  have hc2 := card_biUnion_le (s := S) (t := miss)
  have hsum : ((∑ u ∈ S, (miss u).card : ℕ) : ℝ) ≤ 4 * (ε * n) := by
    push_cast
    calc (∑ u ∈ S, ((miss u).card : ℝ)) ≤ ∑ _u ∈ S, ε * n := sum_le_sum hmiss
      _ = S.card * (ε * n) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ 4 * (ε * n) := by
        apply mul_le_mul_of_nonneg_right (by exact_mod_cast hS) (by positivity)
  have hcR : ((clsT p i).card : ℝ) ≤
      ((PartitionedTriangleAbsorption.TypedEmbeddingSelection.typedNeighbours p G S i).card : ℝ)
        + ((∑ u ∈ S, (miss u).card : ℕ) : ℝ) := by
    exact_mod_cast hc1.trans (Nat.add_le_add_left hc2 _)
  have hlo := hid.1 i
  have : (1 - ε) * n / 4 - 4 * (ε * n) ≥ 1 / 8 * n := by nlinarith
  push_cast at hlo
  linarith

/-- **Terminal omni-absorber for bounded cores on idealized `F₁`-hosts** (produced, no
supplied absorber).  For every core-size bound `K` and every `η > 0` there is `N` such that on
every idealized `F₁`-host (`ε ≤ 1/100`) with `n ≥ N` vertices, for every forbidden edge set `B`
with `Δ(B) ≤ n/40` and every core `X ⊆ E(G)` disjoint from `B` with `|X| ≤ K`, there is
`C ⊆ E(G)` disjoint from `B ∪ X`, decomposable, with `Δ(C) ≤ ηn`, such that `C ∪ L` is
`F₁`-decomposable for every integrally `F₁`-divisible `L ⊆ X`. -/
theorem F1_ideal_terminal_absorber (K : ℕ) (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
      (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 / 100 → IsIdealizedT F1 ε G p →
      ∀ B X : Finset (Sym2 V), DegBounded B (1 / 8 * Fintype.card V / 5) →
        X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
        ∃ C, C ⊆ G.edgeFinset ∧ Disjoint C (B ∪ X) ∧ HasDecomp p F1 C ∧
          DegBounded C (η * Fintype.card V) ∧
          ∀ L ⊆ X, IsIntDiv p F1 L → HasDecomp p F1 (C ∪ L) := by
  obtain ⟨N, hN⟩ := BoundedCoreStage104.exists_uniform_terminal_absorber F1 (by decide)
    TypedTransformer.F1_three_step K (1 / 8) η (by norm_num) hη
  refine ⟨N, fun V _ _ p G _ hn ε hε0 hε1 hid B X hB hXG hXB hK => ?_⟩
  exact hN G p hn (compatibleSupply_F1_of_idealized p G hε0 hε1 hid) B X hB hXG hXB hK

end NashWilliams18
