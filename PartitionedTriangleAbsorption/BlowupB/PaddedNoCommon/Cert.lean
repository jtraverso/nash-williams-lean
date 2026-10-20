/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Universal

set_option exponentiation.threshold 512

/-!
# `UniversalCert` for trivial-lattice families with walks of length four

The scales are the padded ones of `UniversalCert`: `γ = ω`, `δ = paddedAbsDelta ω = ω¹²/2⁶³`,
`ρ = paddedRho ω = ω²⁶/2²⁶²`. The refiner runs at `λ = ω δ / 2⁴⁰ = ω¹³/2¹⁰³` (so `2²⁴ ρ ≤ λ²`),
and the internal-load threshold of the path system is `Q = δ n / 2²⁵`. The supply budget `2^21` and
the terminal budget `2^21` (for pieces of at most `168` edges) are unchanged.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral

/-- The explicit scale inequalities (pure real arithmetic). -/
theorem walk_scales (ω n δ ρ lam Q : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hδ : δ = ω ^ 12 / 2 ^ 63) (hρ : ρ = ω ^ 26 / 2 ^ 262) (hlam : lam = ω * δ / 2 ^ 40)
    (hQ : Q = δ * n / 2 ^ 25) (hn : 1 ≤ ρ * n) :
    0 < lam ∧ lam ≤ 1 / 64 ∧ 0 < ρ ∧ 2 ^ 24 * ρ ≤ lam ^ 2 ∧ 256 ≤ lam * n ∧ 0 < δ ∧ 0 < Q ∧
    3 * (4100 * lam * n ^ 2) / Q + 3 +
      2 * (2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) + 2) < ω * n ∧
    (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * (2 * δ * n) < ω * n / 2 ∧
    (2 ^ 21 : ℝ) ≤ δ * n / 4 ∧
    2 * ρ * n + 4 * lam * n + 2 * (Q + (4096 * lam * n + 1)) ≤ δ * n ∧
    (2 ^ 21 : ℝ) * (4096 * lam * n + 2 * (Q + (4096 * lam * n + 1))) ≤ δ * n / 2 ∧
    4 * (2 * ρ + 16 * lam + 1224 * ρ * 2 ^ 21) ≤ δ * ω := by
  have hA0 : 0 < ω ^ 12 := by positivity
  have hA1 : ω ^ 12 ≤ ω := pow_le_of_le_one hω.le hω1 (by norm_num)
  have hA2 : ω ^ 12 ≤ 1 := hA1.trans hω1
  have h26 : ω ^ 26 = (ω * ω ^ 12) * (ω * ω ^ 12) := by ring
  have hB : ω * ω ^ 12 ≤ ω ^ 12 := mul_le_of_le_one_left hA0.le hω1
  have hB0 : 0 < ω * ω ^ 12 := by positivity
  have hBB : (ω * ω ^ 12) * (ω * ω ^ 12) ≤ ω * ω ^ 12 :=
    mul_le_of_le_one_left hB0.le (hB.trans hA2)
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hρ0 : 0 < ρ := by rw [hρ]; positivity
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have e1 : lam = (ω * ω ^ 12) / 2 ^ 103 := by rw [hlam, hδ]; ring
  have e2 : ρ = (ω * ω ^ 12) * (ω * ω ^ 12) / 2 ^ 262 := by rw [hρ, h26]
  have hρlam : 2 ^ 150 * ρ ≤ lam := by
    rw [e1, e2]; norm_num; linarith
  have hlamsq : 2 ^ 24 * ρ ≤ lam ^ 2 := by
    rw [e1, e2]
    have : ((ω * ω ^ 12) / 2 ^ 103) ^ 2 = (ω * ω ^ 12) * (ω * ω ^ 12) / 2 ^ 206 := by ring
    rw [this]
    have : 0 ≤ (ω * ω ^ 12) * (ω * ω ^ 12) := by positivity
    norm_num; linarith
  have hlamδ : 2 ^ 40 * lam ≤ δ := by
    rw [hlam]; nlinarith
  have hδω : 2 ^ 63 * δ ≤ ω := by rw [hδ]; nlinarith
  have hn0 : 0 < n := by
    by_contra h
    have h' : n ≤ 0 := le_of_not_gt h
    nlinarith
  have hρn : 2 ^ 150 ≤ lam * n := by nlinarith
  have hlamn : 2 ^ 40 * (lam * n) ≤ δ * n := by nlinarith
  have hδn : 2 ^ 63 * (δ * n) ≤ ω * n := by nlinarith
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hdiv : 3 * (4100 * lam * n ^ 2) / Q = 12300 / 2 ^ 15 * ω * n := by
    rw [hQ, hlam]; field_simp; ring
  refine ⟨hlam0, ?_, hρ0, hlamsq, by nlinarith, hδ0, hQ0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · nlinarith
  · rw [hdiv, hQ]; nlinarith
  · nlinarith
  · nlinarith
  · rw [hQ]; nlinarith
  · rw [hQ]; nlinarith
  · nlinarith

/-- **`UniversalCert` without common neighbour classes.** For every family of triangles with a
trivial lattice, `ThreeStepLinks`, walks of length four between any two classes in the allowed-pair
graph, and an explicit witness bound `B` for pieces of at most `168` edges whose terminal order and
size fit into `2^21`. -/
theorem universalCert_of_trivial_walk (F : Finset (Multiset (Fin 4)))
    (hcard : ∀ τ ∈ F, Multiset.card τ = 3) (hthree : ThreeStepLinks F)
    (hwalk : Walk4 (fun i j : Fin 4 => ∃ k, Link F i j k))
    (htriv : TrivialLattice F) (B : ℕ) (hB : WitnessBoundK F 168 B)
    (hord : terminalOrder 168 B 4 ≤ 2 ^ 21) (hsize : terminalSize 168 B ≤ 2 ^ 21) :
    UniversalCert F := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  have hδ : paddedAbsDelta ω = ω ^ 12 / 2 ^ 63 := by
    unfold paddedAbsDelta paddedKappa; ring
  obtain ⟨hlam, hlam64, hrho, hscale, hn2, hδ0, hQ, hpathB, hembed, hfixed, hledgerB, hrootB,
    hcountB⟩ := walk_scales ω (Fintype.card V) (paddedAbsDelta ω) (paddedRho ω)
      (ω * paddedAbsDelta ω / 2 ^ 40) (paddedAbsDelta ω * Fintype.card V / 2 ^ 25) hω hω1 hδ rfl
      rfl rfl hn
  exact universal_budget_walk F hcard hthree hwalk htriv B hB hord hsize p G ω
    (ω * paddedAbsDelta ω / 2 ^ 40) (paddedRho ω) (paddedAbsDelta ω)
    (paddedAbsDelta ω * Fintype.card V / 2 ^ 25) hG hs hlam hlam64 hrho hscale hn hn2 hδ0 hQ
    hpathB hembed hfixed hledgerB hrootB hcountB

end PaddedNoCommon

#print axioms PaddedNoCommon.universal_budget_walk
#print axioms PaddedNoCommon.universalCert_of_trivial_walk
