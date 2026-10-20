/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Uniform
public import PartitionedTriangleAbsorption.BlowupB.Flex.WholeDef

@[expose] public section

/-! The family-dependent real inverse and an existing flexible absorber can use
the same scales. Unlike `decomposition_uniform`, the reserve here shrinks with
the requested absorber degree. This is a consumer of `UniversalCertFlex`, not
a proof that every family has that geometric certificate. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.Flex
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PaddedF12 KeevashQuantitative

/-- A proved flexible family certificate discharges the host-level universal
absorber premise. All numerical choices precede the graph and its weights. -/
theorem decomposition_of_flexible_absorber
    (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (hU : UniversalCertFlex F) (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ ρ ε : ℝ, ∃ N : ℕ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < ε ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
          (∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) →
          GuardedSupply p G (fun i j => ∃ k, Link F i j k)
            (2 ^ 21) (ω * Fintype.card V) →
          IsIntDiv p F G.edgeFinset →
          ∀ φ : Finset V → ℝ,
          (∀ T, IsCopy p F G T →
            ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V) →
          (∀ e ∈ G.edgeFinset,
            |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) →
          HasDecomp p F G.edgeFinset := by
  set C := generalInverseConstant F hF.card_three
  have hC : 0 ≤ C := (generalInverseConstant_pos F hF.card_three).le
  set κ := inverseKappa C ω
  have hκ : 0 < κ := (inverse_scales_pos hC hω).1
  have hκω : κ ≤ ω / 8 := min_le_left _ _
  refine ⟨min (ω / (2 : ℝ)^63) (κ / 8), by positivity, ?_⟩
  intro δ hδ hδmax
  have hδκ : δ ≤ κ / 8 := hδmax.trans (min_le_right _ _)
  have hδω : (2 : ℝ)^63 * δ ≤ ω := by
    have hd := hδmax.trans (min_le_left _ _)
    have hd' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^63)).mp hd
    nlinarith
  set ρ := min (κ / 8) ((ω * δ / (2 : ℝ)^48)^2 / (2 : ℝ)^24)
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρκ : ρ ≤ κ / 8 := min_le_left _ _
  have hρ1 : ρ ≤ 1 := by linarith
  have hρsq : (2 : ℝ)^24 * ρ ≤ (ω * δ / (2 : ℝ)^48)^2 := by
    have hr : ρ ≤ (ω * δ / (2 : ℝ)^48)^2 / (2 : ℝ)^24 := min_le_right _ _
    have hr' := (le_div_iff₀ (by positivity : (0 : ℝ) < 2^24)).mp hr
    nlinarith
  set ε := min (inverseEpsilon C ω)
    (loadTolerance (min (ω / 8) (min 1 (ω^2)))) / 2
  have hmin : 0 < min (inverseEpsilon C ω)
      (loadTolerance (min (ω / 8) (min 1 (ω^2)))) :=
    lt_min (inverse_scales_pos hC hω).2 (initial_loadTolerance_pos hω)
  have hε : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ρ, ε, max (scaledOrder ω ρ) ⌈1 / ρ⌉₊, hρ, hρ1, hε, ?_⟩
  intro V _ _ hN p G _ hG hs hdiv φ hw hload
  have hn : scaledOrder ω ρ ≤ Fintype.card V := (le_max_left _ _).trans hN
  have hnρ : 1 ≤ ρ * (Fintype.card V : ℝ) := by
    have hn' : ⌈1 / ρ⌉₊ ≤ Fintype.card V := (le_max_right _ _).trans hN
    have hh : 1 / ρ ≤ (Fintype.card V : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn')
    have hh' := (div_le_iff₀ hρ).mp hh
    nlinarith
  have hsc : FlexScales ω δ ρ (Fintype.card V) :=
    ⟨hω, hω1, hδ, hδω, hρsq, Nat.cast_nonneg _, hnρ⟩
  have hnum : ScaledNumericInputs (Fintype.card V) C ω ε ρ δ :=
    scaled_numeric_inputs_of_order C ω ε ρ δ hC hω hω1 hε.le hρ hρ1
      (by dsimp [ε]; linarith) (by linarith) _ hn
  exact decomposition_general F hF ω ε ρ δ V hnum p G
    (hU V p G ω δ ρ hsc hG hs) hG (hs.mono (by norm_num) le_rfl)
    hdiv φ hw hload

#print axioms decomposition_of_flexible_absorber

end PaddedGeneral.RealInverse
