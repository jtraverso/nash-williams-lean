/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.RoutedPaper
public import PartitionedTriangleAbsorption.BlowupB.Families
public import PartitionedTriangleAbsorption.FourColourStabilityStage84
public import PartitionedTriangleAbsorption.TypedCoarseningStage81

@[expose] public section

/-! The four-colour application, using Paper II's proved F3 producer. -/

namespace NashWilliams18.PaperII

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.BlowupB
open PartitionedTriangleAbsorption.ClassRepresentativesStage65
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedCoarseningStage81
open PartitionedTriangleAbsorption.FourColourStabilityStage84
open PartitionedTriangleAbsorption.FourClassDivisibilityStage82

private theorem missing_degree_bound {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (c : G.Coloring (Fin 4))
    (eps : ℝ) (heps : 0 ≤ eps)
    (hdeg : ∀ v, (3 / 4 - eps) * Fintype.card V ≤ (G.degree v : ℝ)) (v : V) :
    (missDeg c F3 G v : ℝ) ≤ 4 * eps * Fintype.card V := by
  classical
  have hs : missSet c F3 G v = (host c).neighborFinset v \ G.neighborFinset v := by
    ext w
    simp only [missSet, mem_filter, mem_univ, true_and, mem_sdiff,
      SimpleGraph.mem_neighborFinset, allowedPair_F3_iff]
    change (v ≠ w ∧ c v ≠ c w ∧ ¬G.Adj v w) ↔ (c v ≠ c w ∧ ¬G.Adj v w)
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fun he => h.1 (congrArg c he), h⟩
  have hsub : G.neighborFinset v ⊆ (host c).neighborFinset v := by
    intro w hw
    simp only [SimpleGraph.mem_neighborFinset] at hw ⊢
    exact c.valid hw
  have hle : G.degree v ≤ (host c).degree v := G.degree_le_of_le (fun _ _ h => c.valid h)
  have hcount : missDeg c F3 G v + G.degree v + (classSet c (c v)).card =
      Fintype.card V := by
    unfold missDeg
    rw [hs, card_sdiff_of_subset hsub, SimpleGraph.card_neighborFinset_eq_degree,
      SimpleGraph.card_neighborFinset_eq_degree]
    have hh := host_degree_add_class (c : V → Fin 4) v
    omega
  have hcountR : (missDeg c F3 G v : ℝ) + G.degree v + (classSet c (c v)).card =
      Fintype.card V := by exact_mod_cast hcount
  have hlo := class_lower G c eps heps hdeg (c v)
  nlinarith [hdeg v]

theorem margin_four_colour_decomposition :
    ∃ eps : ℝ, 0 < eps ∧ eps ≤ 1 / 16 ∧ ∃ N : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W], N ≤ Fintype.card W →
        ∀ (G : SimpleGraph W) [DecidableRel G.Adj] (c : G.Coloring (Fin 4)),
          (3 / 4 - eps) * Fintype.card W ≤ (G.minDegree : ℝ) →
          (∀ v, Even (G.degree v)) →
          (edgeVec c G.edgeFinset 0 1 + edgeVec c G.edgeFinset 2 3 =
            edgeVec c G.edgeFinset 0 2 + edgeVec c G.edgeFinset 1 3) →
          (edgeVec c G.edgeFinset 0 1 + edgeVec c G.edgeFinset 2 3 =
            edgeVec c G.edgeFinset 0 3 + edgeVec c G.edgeFinset 1 2) →
          ∃ D, IsDecomp c F3 G.edgeFinset D ∧
            IsDecomp (merge ∘ c) F0 G.edgeFinset D := by
  obtain ⟨eta, heta, N, delta, hdelta, happ⟩ :=
    PaddedGeneral.RealInverse.nearlyComplete_F123 (F := F3) (Or.inr (Or.inr rfl))
  let eps := min (1 / 16) (min (eta / 3) (delta / 4))
  have heps : 0 < eps := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have heta' : 3 * eps ≤ eta := by
    have hh : eps ≤ eta / 3 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hdelta' : 4 * eps ≤ delta := by
    have hh : eps ≤ delta / 4 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨eps, heps, min_le_left _ _, max N 1, ?_⟩
  intro W _ _ hW G _ c hmin heven hbal1 hbal2
  classical
  have hdeg : ∀ v, (3 / 4 - eps) * Fintype.card W ≤ (G.degree v : ℝ) :=
    fun v => hmin.trans (by exact_mod_cast G.minDegree_le_degree v)
  let d : ℕ := ⌊4 * eps * Fintype.card W⌋₊
  have hmiss : ∀ v, missDeg c F3 G v ≤ d := fun v =>
    Nat.le_floor (missing_degree_bound G c eps heps.le hdeg v)
  have hd : (d : ℝ) ≤ delta * Fintype.card W := by
    have hf : (d : ℝ) ≤ 4 * eps * Fintype.card W :=
      Nat.floor_le (show (0 : ℝ) ≤ 4 * eps * Fintype.card W by positivity)
    exact hf.trans (mul_le_mul_of_nonneg_right hdelta' (Nat.cast_nonneg _))
  have hclasses : ∀ i, (1 / 4 - eta) * Fintype.card W ≤ ((classSet c i).card : ℝ) ∧
      ((classSet c i).card : ℝ) ≤ (1 / 4 + eta) * Fintype.card W := by
    intro i
    have hl := class_lower G c eps heps.le hdeg i
    have hu := class_upper G c eps heps.le hdeg i
    have hmul := mul_le_mul_of_nonneg_right heta' (Nat.cast_nonneg (Fintype.card W) : (0 : ℝ) ≤ _)
    have hn0 : (0 : ℝ) ≤ Fintype.card W := Nat.cast_nonneg _
    constructor <;> nlinarith [mul_nonneg heps.le hn0]
  have hcross : StructuralF3.CrossClass c G.edgeFinset := fun _ _ he =>
    c.valid (SimpleGraph.mem_edgeFinset.mp he)
  have hdiv : IsIntDiv c F3 G.edgeFinset :=
    (isIntDiv_iff_counts c G.edgeFinset hcross).mpr
      ⟨fun v => by rw [incident_edgeFinset]; exact heven v, hbal1, hbal2⟩
  obtain ⟨D, hD⟩ := happ G c d (le_of_max_le_left hW)
    (fun u v huv => (allowedPair_F3_iff _ _).mpr (c.valid huv)) hmiss hd hclasses hdiv
  exact ⟨D, hD, F3_decomp_as_F0 c hD⟩

#print axioms margin_four_colour_decomposition

end NashWilliams18.PaperII
