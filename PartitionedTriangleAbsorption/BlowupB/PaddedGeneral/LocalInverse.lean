/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.LocalProfiles
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.ReductionLarge

@[expose] public section

/-! # Corrected complete inverse contract and its actual load-defect consumer

The new contract includes both global and local real compatibility. Old contracts
remain unchanged for the already established special families. A producer of this
new contract is still required; nothing in this file assumes its conclusion for free.
-/

namespace PaddedGeneral

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

/-- Corrected certificate, retaining the large-class threshold and quantitative bound. -/
def CompleteInverseCertLocal (F : Finset (Multiset (Fin 4))) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4) (r : Sym2 V → ℝ) (ε γ : ℝ),
    0 ≤ ε → 0 < γ → γ ≤ 1 → 8 ≤ γ * (Fintype.card V : ℝ) →
    (∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i) →
    Sym2DemandSupported p F r → (∀ e, |r e| ≤ ε) → FullSpanCompat p F r →
    ∃ z : TriangleChain V, CopySupported p F (activeCompleteGraph p F) z ∧
      boundary z = r ∧
      ∀ T, |z T| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ))

theorem CompleteInverseCert₈.toLocal {F : Finset (Multiset (Fin 4))}
    (hI : CompleteInverseCert₈ F) : CompleteInverseCertLocal F := by
  intro V _ _ p r ε γ hε hγ hγ1 hlarge hmin hs hr hc
  exact hI V p r ε γ hε hγ hγ1 hlarge hmin hs hr hc.1

theorem CompleteInverseCert.toLocal {F : Finset (Multiset (Fin 4))}
    (hI : CompleteInverseCert F) : CompleteInverseCertLocal F :=
  (completeInverseCert₈_of_cert hI).toLocal

/-- Deleting a decomposable reserve preserves the added compatibility. This
matches the graph on which `hostRepair_gen` actually forms its defect. -/
theorem loadDefect_deleteEdges_fullSpan {V : Type} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (B : Finset (Sym2 V))
    (φ : TriangleChain V) (hdiv : IsIntDiv p F G.edgeFinset)
    (hB : HasDecomp p F B) (hBG : B ⊆ G.edgeFinset) :
    FullSpanCompat p F (loadDefect p F (G.deleteEdges (B : Set (Sym2 V))) φ) := by
  apply loadDefect_fullSpan
  rw [SimpleGraph.edgeFinset_deleteEdges]
  exact isIntDiv_sdiff_of_hasDecomp hdiv hB hBG

/-- Transfer to the host uses the corrected compatibility, not global totals alone. -/
theorem exists_host_chain_inverse_local (F : Finset (Multiset (Fin 4)))
    (hI : CompleteInverseCertLocal F) {V : Type} [Fintype V] [DecidableEq V] (p : V → Fin 4)
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
        |w T| ≤ ((2 : ℝ) ^ 32 / ω ^ 9) * ε / Fintype.card V := by
  classical
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  obtain ⟨z, hzs, hzr, hzb⟩ := hI V p r ε ω hε hω hω1 hlarge hmin hs hr hc
  let M : ℝ := (2 : ℝ) ^ 20 * ε / (ω ^ 6 * Fintype.card V)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hS := total_mass_bound p F (activeCompleteGraph p F) z M hM (fun T _ => hzb T)
  have hU := vertex_mass_bound p F (activeCompleteGraph p F) z M hM (fun T _ => hzb T)
  obtain ⟨w, hws, hwr, hwb⟩ := SignedTransfer.exists_signed_transfer p F G
    (ω * Fintype.card V / 2) ε ((Fintype.card V : ℝ) ^ 3 * M)
    ((Fintype.card V : ℝ) ^ 2 * M) (by positivity) hguard z hzs
    (by intro e he; rw [hzr]; exact hzero e he)
    (by intro e; rw [hzr]; exact hr e) hS hU
  refine ⟨w, hws, hwr.trans hzr, ?_⟩
  intro T hT
  exact (hwb T hT.1.card_eq).trans (transferred_inverse_bound ε ω (Fintype.card V)
    hε hω hω1 hnR)

/-- The pipeline supplies all compatibility premises, even after a decomposable
reserve has been deleted (apply this to that residual graph). -/
theorem exists_loadDefect_correction_local (F : Finset (Multiset (Fin 4)))
    (hI : CompleteInverseCertLocal F) {V : Type} [Fintype V] [DecidableEq V]
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
        |w T| ≤ ((2 : ℝ) ^ 32 / ω ^ 9) * ε / Fintype.card V :=
  exists_host_chain_inverse_local F hI p G (loadDefect p F G φ) ε ω
    hε hω hω1 hlarge hmin hguard (loadDefect_supported p F G φ hactive)
    (loadDefect_zero p F G φ) (loadDefect_bound p F G φ ε hε hloads)
    (loadDefect_fullSpan p F G φ hdiv)

#print axioms CompleteInverseCert₈.toLocal
#print axioms loadDefect_deleteEdges_fullSpan
#print axioms exists_host_chain_inverse_local
#print axioms exists_loadDefect_correction_local

end PaddedGeneral
