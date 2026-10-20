/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.TerminalAbsorberF1
import PartitionedTriangleAbsorption.F1PackingGuardStage215

/-!
# Theorem 14.7 for `F₁`: the guarded private library on idealized hosts (ported Stage 215)

This file applies the ported producer
`PartitionedTriangleAbsorption.F1PackingGuardStage215.exists_uniform_F1_guarded_library`
to the idealized `F₁`-hosts of `Theorem147F1Statement`.

Translations: class sizes with `α = 1/8` (first clause of `IsIdealizedT`, `ε ≤ 1/100`);
non-neighbours in admissible classes `≤ ε n ≤ δ n` (third clause, via
`admissiblePair_iff_allowedT_F1` and `card_nonNbr_add_degT`), where `δ` is the tolerance returned
by Stage 215, so the host tolerance is `ε₀ = min δ (1/100)`.

Constants: `μ`, `ε₀`, `N` depend only on `η` and the piece bound `m`; they are fixed before the
host, the packing `D`, the library `(P i)` and the forbidden set `B`.

**What this gives and what it does not.**  It is a *producer*: disjoint private absorbers
`A i` (decomposable, `A i ∪ P i` decomposable, avoiding `B`), physically built in `G`, such that
the closure of `⋃ A i` with respect to the SAME packing `D` (the absorbers plus every triangle of
`D` they touch) has maximum degree `≤ η n`.  It does **not** decompose the freed complement
`closure D (⋃ A i) \ ⋃ A i`; see `NW18_BRANCH_LEDGER.md` §0quater for why that complement has the
same shape as the Stage 205 residual.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)
open PartitionedTriangleAbsorption.PackingPrivateClosureStage213 (closure)

/-- **Guarded private library on idealized `F₁`-hosts** (Stage 215, produced).  For every
`η > 0` and piece bound `m` there are `μ > 0`, `ε₀ ∈ (0, 1/100]` and `N` such that on every
idealized `F₁`-host (`ε ≤ ε₀`) with `n ≥ N` vertices, for every `F₁`-decomposition `D` of an edge
set `Q ⊆ E(G)`, every library of integrally divisible pieces `P i ⊆ E(G)` (`i ∈ s`) of size
`≤ m` with total incidence `≤ μ n` at every vertex and `|s| ≤ μ² n²`, and every forbidden set
`B` with `Δ(B) ≤ 3 μ n`, there are pairwise disjoint absorbers `A i ⊆ E(G) \ B` with `A i` and
`A i ∪ P i` decomposable, whose closure with respect to `D` lies in `E(G)` and has maximum degree
`≤ η n`. -/
theorem F1_ideal_guarded_library (η : ℝ) (hη : 0 < η) (m : ℕ) :
    ∃ μ ε₀ : ℝ, 0 < μ ∧ 0 < ε₀ ∧ ε₀ ≤ 1 / 100 ∧ ∃ N : ℕ,
      ∀ (V I : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
        (G : SimpleGraph V) [DecidableRel G.Adj], N ≤ Fintype.card V →
      ∀ ε : ℝ, ε ≤ ε₀ → IsIdealizedT F1 ε G p →
      ∀ (Q : Finset (Sym2 V)) (D : Finset (Finset V)),
      Q ⊆ G.edgeFinset → IsDecomp p F1 Q D →
      ∀ (s : Finset I) (P : I → Finset (Sym2 V)) (B : Finset (Sym2 V)),
      DegBounded B (3 * μ * Fintype.card V) →
      (∀ i ∈ s, P i ⊆ G.edgeFinset ∧ (P i).card ≤ m ∧ IsIntDiv p F1 (P i)) →
      (∀ v, (∑ i ∈ s, AntiEdgeSelection.incidentLoad (P i) v : ℕ) ≤ μ * Fintype.card V) →
      (s.card : ℝ) ≤ μ ^ 2 * (Fintype.card V : ℝ) ^ 2 →
      ∃ A : I → Finset (Sym2 V),
        (∀ i ∈ s, A i ⊆ G.edgeFinset ∧ Disjoint (A i) B ∧
          HasDecomp p F1 (A i) ∧ HasDecomp p F1 (A i ∪ P i)) ∧
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (A i) (A j)) ∧
        closure D (s.biUnion A) ⊆ G.edgeFinset ∧
        DegBounded (closure D (s.biUnion A)) (η * Fintype.card V) := by
  obtain ⟨μ, δ, hμ, hδ, N, hN⟩ :=
    F1PackingGuardStage215.exists_uniform_F1_guarded_library (1 / 8) η (by norm_num) hη m
  refine ⟨μ, min δ (1 / 100), hμ, lt_min hδ (by norm_num), min_le_right _ _, max N 1, ?_⟩
  intro V I _ _ p G _ hn ε hε hid Q D hQ hD s P B hB hP hload hmass
  have hnpos : 0 < Fintype.card V := lt_of_lt_of_le (by omega) hn
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hεδ : ε ≤ δ := hε.trans (min_le_left _ _)
  have hε1 : ε ≤ 1 / 100 := hε.trans (min_le_right _ _)
  apply hN V I ((le_max_left _ _).trans hn) p G
  · intro k
    have h := hid.1 k
    have e : ((univ.filter fun v => p v = k).card : ℝ) = ((clsT p k).card : ℝ) := rfl
    rw [e]
    have : (1 - ε) * (Fintype.card V : ℝ) / 4 ≥ 1 / 8 * Fintype.card V := by nlinarith
    push_cast at h
    linarith
  · intro i j hij x hx
    have hal : AllowedT F1 (p x) j := by
      rw [hx]; exact (admissiblePair_iff_allowedT_F1 i j).mp hij
    have h1 := hid.2.2 x j hal
    have h2 := card_nonNbr_add_degT G p x j
    have h2' : ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) +
        (degT G p x j : ℝ) = ((clsT p j).card : ℝ) := by exact_mod_cast h2
    have h3 : ε * (Fintype.card V : ℝ) ≤ δ * Fintype.card V :=
      mul_le_mul_of_nonneg_right hεδ hnR.le
    linarith
  · exact hQ
  · exact hD
  · exact hB
  · exact hP
  · exact hload
  · exact hmass

end NashWilliams18
