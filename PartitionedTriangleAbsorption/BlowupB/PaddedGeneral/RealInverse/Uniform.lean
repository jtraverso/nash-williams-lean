/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Consumer

@[expose] public section

/-! # Uniform parameters for the real-inverse consumers

The parameters of the reserve/repair/nibble pipeline are chosen here from
`F` and `ω` (and `δ`) **before** the host, using the family constant
`C = generalInverseConstant F _` of the proved general real inverse:

* `κ = inverseKappa C ω`, `δ₀ = κ / 8`, `ρ = κ / 8`;
* `ε = min (inverseEpsilon C ω) (loadTolerance (min (ω/8) (min 1 (ω^2)))) / 2`;
* `N = scaledOrder ω ρ`.

`decomposition_uniform` has no `ScaledNumericInputs`, no
`CompleteInverseCertLocalBound` and no numerical budget among its premises.
It is still **conditional**: `UniversalAbsorbers p F G ρ δ` is an explicit
remaining geometric input, together with the graph/weight hypotheses.

`hostRepair_uniform` is the robust fractional repair with `ε₀, κ₀, N` chosen
from `F, ω` before `G, B, φ`. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble
open PaddedF12 PaddedF12.PaddedThresholds KeevashQuantitative

/-- The uniform load tolerance of the initial (nibble) stage. -/
theorem initial_loadTolerance_pos {ω : ℝ} (hω : 0 < ω) :
    0 < loadTolerance (min (ω / 8) (min 1 (ω ^ 2))) :=
  loadTolerance_pos _ (by positivity) ((min_le_right _ _).trans (min_le_left _ _))

/-- **Uniform conditional decomposition with chosen constants.**

For every family `F` with `FamilyFacts F` and every `0 < ω ≤ 1` there is
`δ₀ > 0` such that for every `0 < δ ≤ δ₀` there are `0 < ρ ≤ 1`, `ε > 0` and
`N`, depending only on `F, ω, δ`, such that every host with at least `N`
vertices, active edges, guarded supply of order 4 at `ω n`, integer
divisibility, universal absorbers `UniversalAbsorbers p F G ρ δ` and
actual-copy fractional weights in `[ω²/n, (27/ω)/n]` with edge-load error
`≤ ε` is decomposable.

`UniversalAbsorbers` is an explicit remaining geometric hypothesis.
(The hypothesis `0 < δ` was requested in the statement; the proof does not
need it.) -/
theorem decomposition_uniform (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      ∃ ρ ε : ℝ, ∃ N : ℕ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < ε ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
          (∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) →
          GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 (ω * Fintype.card V) →
          IsIntDiv p F G.edgeFinset →
          UniversalAbsorbers p F G ρ δ →
          ∀ φ : Finset V → ℝ,
          (∀ T, IsCopy p F G T →
            ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V) →
          (∀ e ∈ G.edgeFinset,
            |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) →
          HasDecomp p F G.edgeFinset := by
  set C := generalInverseConstant F hF.card_three
  have hC : 0 ≤ C := (generalInverseConstant_pos F hF.card_three).le
  set κ := inverseKappa C ω with hκdef
  have hκ : 0 < κ := (inverse_scales_pos hC hω).1
  have hκω : κ ≤ ω / 8 := min_le_left _ _
  refine ⟨κ / 8, by positivity, fun δ _ hδ => ?_⟩
  set ρ := κ / 8 with hρdef
  set ε := min (inverseEpsilon C ω) (loadTolerance (min (ω / 8) (min 1 (ω ^ 2)))) / 2
    with hεdef
  have hρ : 0 < ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    have : ω / 8 ≤ 1 := by linarith
    have : κ / 8 ≤ κ := by linarith
    linarith
  have hmin : 0 < min (inverseEpsilon C ω) (loadTolerance (min (ω / 8) (min 1 (ω ^ 2)))) :=
    lt_min (inverse_scales_pos hC hω).2 (initial_loadTolerance_pos hω)
  have hε : 0 < ε := by positivity
  refine ⟨ρ, ε, scaledOrder ω ρ, hρ, hρ1, hε, ?_⟩
  intro V _ _ hN p G _ hG hs hdiv hU φ hw hload
  have hn : ScaledNumericInputs (Fintype.card V) C ω ε ρ δ :=
    scaled_numeric_inputs_of_order C ω ε ρ δ hC hω hω1 hε.le hρ hρ1
      (by rw [hεdef]; linarith) (by rw [← hκdef]; linarith) _ hN
  exact decomposition_general F hF ω ε ρ δ V hn p G hU hG hs hdiv φ hw hload

/-- **Uniform robust fractional repair, explicit form.** With the family
constant `C = generalInverseConstant F _` fixed by `F`, every deletion `B` of
maximum degree `≤ κ n` with `0 ≤ κ ≤ inverseKappa C ω` and every load error
`ε ≤ inverseEpsilon C ω` is repaired. No inverse hypothesis and no budget
inequality remains. -/
theorem hostRepair_uniform_explicit (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (ω ε κ : ℝ) (φ : Finset V → ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hε : 0 ≤ ε) (hlarge : 8 ≤ ω * Fintype.card V)
    (hallowed : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 (ω * Fintype.card V))
    (hdiv : IsIntDiv p F G.edgeFinset)
    (hBG : B ⊆ G.edgeFinset) (hBdec : HasDecomp p F B)
    (hBdeg : DegBounded B (κ * Fintype.card V))
    (hw : ∀ T, IsCopy p F G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε)
    (hεC : ε ≤ inverseEpsilon (generalInverseConstant F hF) ω)
    (hκ : 0 ≤ κ) (hκC : κ ≤ inverseKappa (generalInverseConstant F hF) ω) :
    ∃ ψ : Finset V → ℝ,
      (∀ T, IsCopy p F (G.deleteEdges (B : Set (Sym2 V))) T →
        0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
      ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        (∑ T ∈ copies p F (G.deleteEdges (B : Set (Sym2 V))) with e ∈ triEdges T, ψ T) = 1 := by
  have hC := (generalInverseConstant_pos F hF).le
  have hk := inverse_kappa_budget hC hω hκC
  exact hostRepair_general F hF V p G B ω ε κ φ hω hω1 hε hlarge hallowed hs hdiv hBG hBdec
    hBdeg hw hload (inverse_epsilon_budget hC hω hεC) hκ hk.1 hk.2

/-- **Uniform robust fractional repair.** For every `F` whose members have
cardinality three and every `0 < ω ≤ 1`, there are `ε₀ > 0`, `κ₀ > 0` and `N`,
chosen before `G`, `B` and `φ`, such that on every host with at least `N`
vertices, active edges, guarded supply of order 4 at `ω n` and integer
divisibility, every decomposable `B ⊆ E(G)` of maximum degree `≤ κ₀ n` and every
actual-copy fractional weight in `[ω²/n, (27/ω)/n]` with load error `≤ ε₀`
yields an exact fractional decomposition of `G - B` with weights in
`[0, (54/ω)/n]`. -/
theorem hostRepair_uniform (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) (ω : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1) :
    ∃ ε₀ κ₀ : ℝ, ∃ N : ℕ, 0 < ε₀ ∧ 0 < κ₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
        (B : Finset (Sym2 V)) (φ : Finset V → ℝ),
        (∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k) →
        GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 (ω * Fintype.card V) →
        IsIntDiv p F G.edgeFinset →
        B ⊆ G.edgeFinset → HasDecomp p F B →
        DegBounded B (κ₀ * Fintype.card V) →
        (∀ T, IsCopy p F G T →
          ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V) →
        (∀ e ∈ G.edgeFinset,
          |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε₀) →
        ∃ ψ : Finset V → ℝ,
          (∀ T, IsCopy p F (G.deleteEdges (B : Set (Sym2 V))) T →
            0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
          ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
            (∑ T ∈ copies p F (G.deleteEdges (B : Set (Sym2 V))) with e ∈ triEdges T,
              ψ T) = 1 := by
  have hC := (generalInverseConstant_pos F hF).le
  obtain ⟨hκ, hε⟩ := inverse_scales_pos hC hω
  refine ⟨inverseEpsilon (generalInverseConstant F hF) ω,
    inverseKappa (generalInverseConstant F hF) ω, ⌈8 / ω⌉₊, hε, hκ, ?_⟩
  intro V _ _ hN p G _ B φ hG hs hdiv hBG hBdec hBdeg hw hload
  have hlarge : 8 ≤ ω * Fintype.card V := by
    have h : 8 / ω ≤ (Fintype.card V : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hN)
    rw [div_le_iff₀ hω] at h
    linarith
  exact hostRepair_uniform_explicit F hF V p G B ω _ _ φ hω hω1 hε.le hlarge hG hs hdiv hBG
    hBdec hBdeg hw hload le_rfl hκ.le le_rfl

end PaddedGeneral.RealInverse
