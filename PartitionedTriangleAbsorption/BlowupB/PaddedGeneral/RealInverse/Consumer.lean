/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Producer
import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.ScaledPipeline

/-! # Connection of the proved general real inverse to the existing consumers

`generalInverseConstant F hF` is the constant produced by
`exists_completeInverseCertLocalBound`. It discharges the hypothesis
`CompleteInverseCertLocalBound F C` of the existing host consumers:

* `exists_host_chain_inverse_general` and `exists_loadDefect_correction_general`
  (host transport, constant `hostInverseConstant C / ω ^ 9 = (18 + 1188 C) / ω ^ 9`);
* `hostRepair_general`;
* `decomposition_general`, the reserve/repair/nibble pipeline.

The last two remain conditional on their other explicit inputs (universal
absorbers, guarded supply, numeric inputs, divisibility, fractional weights);
only the inverse hypothesis is removed. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PaddedF12 PaddedF12.PaddedThresholds KeevashQuantitative

/-- The family constant of the general real inverse. -/
def generalInverseConstant (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) : ℝ :=
  Classical.choose (exists_completeInverseCertLocalBound F hF)

theorem generalInverseConstant_pos (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) : 0 < generalInverseConstant F hF :=
  (Classical.choose_spec (exists_completeInverseCertLocalBound F hF)).1

theorem completeInverseCertLocalBound_general (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3) :
    CompleteInverseCertLocalBound F (generalInverseConstant F hF) :=
  (Classical.choose_spec (exists_completeInverseCertLocalBound F hF)).2

theorem exists_host_chain_inverse_general (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Sym2 V → ℝ) (ε ω : ℝ) (hε : 0 ≤ ε) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlarge : 8 ≤ ω * (Fintype.card V : ℝ))
    (hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i)
    (hguard : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4
      (ω * Fintype.card V / 2))
    (hs : Sym2DemandSupported p F r) (hzero : ∀ e, e ∉ G.edgeFinset → r e = 0)
    (hr : ∀ e, |r e| ≤ ε) (hc : FullSpanCompat p F r) :
    ∃ w : TriangleChain V, CopySupported p F G w ∧ boundary w = r ∧
      ∀ T, IsCopy p F G T →
        |w T| ≤ (hostInverseConstant (generalInverseConstant F hF) / ω ^ 9) * ε /
          Fintype.card V :=
  exists_host_chain_inverse_local_bound F _ (generalInverseConstant_pos F hF).le
    (completeInverseCertLocalBound_general F hF) p G r ε ω hε hω hω1 hlarge hmin hguard
    hs hzero hr hc

theorem exists_loadDefect_correction_general (F : Finset (Multiset (Fin 4)))
    (hF : ∀ τ ∈ F, Multiset.card τ = 3)
    {V : Type} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : TriangleChain V) (ε ω : ℝ) (hε : 0 ≤ ε) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlarge : 8 ≤ ω * (Fintype.card V : ℝ))
    (hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i)
    (hguard : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4
      (ω * Fintype.card V / 2))
    (hactive : G ≤ activeCompleteGraph p F) (hdiv : IsIntDiv p F G.edgeFinset)
    (hloads : ∀ e ∈ G.edgeFinset,
      |1 - ∑ T ∈ copies p F G with e ∈ triEdges T, φ T| ≤ ε) :
    ∃ w : TriangleChain V, CopySupported p F G w ∧
      boundary w = loadDefect p F G φ ∧
      ∀ T, IsCopy p F G T →
        |w T| ≤ (hostInverseConstant (generalInverseConstant F hF) / ω ^ 9) * ε /
          Fintype.card V :=
  exists_loadDefect_correction_local_bound F _ (generalInverseConstant_pos F hF).le
    (completeInverseCertLocalBound_general F hF) p G φ ε ω hε hω hω1 hlarge hmin hguard
    hactive hdiv hloads

theorem hostRepair_general (F : Finset (Multiset (Fin 4)))
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
    (hεbudget : (hostInverseConstant (generalInverseConstant F hF) / ω ^ 9) * ε ≤ ω ^ 2 / 4)
    (hκ : 0 ≤ κ) (hκcap : κ ≤ ω / 8)
    (hκbudget : (hostInverseConstant (generalInverseConstant F hF) / ω ^ 9) *
      (2 * (27 / ω) * κ) ≤ ω ^ 2 / 4) :
    ∃ ψ : Finset V → ℝ,
      (∀ T, IsCopy p F (G.deleteEdges (B : Set (Sym2 V))) T →
        0 ≤ ψ T ∧ ψ T ≤ (54 / ω) / Fintype.card V) ∧
      ∀ e ∈ (G.deleteEdges (B : Set (Sym2 V))).edgeFinset,
        (∑ T ∈ copies p F (G.deleteEdges (B : Set (Sym2 V))) with e ∈ triEdges T, ψ T) = 1 :=
  hostRepair_local_bound F _ (generalInverseConstant_pos F hF).le
    (completeInverseCertLocalBound_general F hF) V p G B ω ε κ φ hω hω1 hε hlarge
    hallowed hs hdiv hBG hBdec hBdeg hw hload hεbudget hκ hκcap hκbudget

/-- The scaled pipeline with the proved inverse. Universal absorbers and the
other inputs remain explicit hypotheses. -/
theorem decomposition_general (F : Finset (Multiset (Fin 4))) (hF : FamilyFacts F)
    (ω ε ρ δ : ℝ) (V : Type) [Fintype V] [DecidableEq V]
    (hn : ScaledNumericInputs (Fintype.card V)
      (generalInverseConstant F hF.card_three) ω ε ρ δ)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hU : UniversalAbsorbers p F G ρ δ)
    (hG : ∀ a b, G.Adj a b → ∃ k, Link F (p a) (p b) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4 (ω * Fintype.card V))
    (hdiv : IsIntDiv p F G.edgeFinset) (φ : Finset V → ℝ)
    (hw : ∀ T, IsCopy p F G T →
      ω ^ 2 / Fintype.card V ≤ φ T ∧ φ T ≤ (27 / ω) / Fintype.card V)
    (hload : ∀ e ∈ G.edgeFinset,
      |(∑ T ∈ copies p F G with e ∈ triEdges T, φ T) - 1| ≤ ε) :
    HasDecomp p F G.edgeFinset :=
  decomposition_local_scaled F hF _ ω ε ρ δ
    (completeInverseCertLocalBound_general F hF.card_three) V hn p G hU hG hs hdiv φ hw hload

end PaddedGeneral.RealInverse
