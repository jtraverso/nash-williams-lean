/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.R2Refiner
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalCharge
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.HostInputs
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.GuardedTokens

@[expose] public section

/-! # The actual F1 and F2 shared refiners in guarded hosts

All algebra and both physical token supplies are instantiated here. The host
is constrained only by permitted pairs and guarded extension supply.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge
open PartitionedTriangleAbsorption.StructuralF3General

inductive Family
  | one
  | two
deriving DecidableEq, Repr

def Family.types : Family → Finset (Multiset (Fin 4))
  | .one => F1
  | .two => F2

def Family.matrix : Family → Fin 4 → Fin 4 → ℤ
  | .one => chi1
  | .two => chi2

theorem Family.card_three (kind : Family) : ∀ τ ∈ kind.types, Multiset.card τ = 3 := by
  cases kind
  · exact ColouredHub.F1_card_three
  · exact ColouredHub.F2_card_three

theorem Family.three_step (kind : Family) : ThreeStepLinks kind.types := by
  cases kind
  · exact F1_three_step
  · exact F2_three_step

theorem Family.common (kind : Family) : ∀ a b : Fin 4, ∃ c,
    (∃ k, Link kind.types a c k) ∧ (∃ k, Link kind.types b c k) := by
  cases kind
  · exact f1_allowed_common
  · exact f2_allowed_common

variable {V : Type*} [Fintype V] [DecidableEq V]

def Family.Good (kind : Family) (p : V → Fin 4) : Finset (Sym2 V) → Prop :=
  match kind with
  | .one => F1Good p
  | .two => F2Good p

def Family.parity (kind : Family) (p : V → Fin 4) : ParityEvaluation (kind.Good p) :=
  match kind with
  | .one => f1Parity p
  | .two => f2Parity p

theorem f1Algebra (p : V → Fin 4) : R2Algebra p F1 chi1 (F1Good p) (f1Parity p) where
  chi_bound := chi1_bound
  charge_dvd := fun A hloop hact hthree => twelve_dvd_chi1 p A hact hloop hthree.2 hthree.1
  good_iff := by
    intro A
    constructor
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1, by
        rw [← f1FreeCharge_eq_original p A h.2.1]
        exact h.2.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1, by
        rw [f1FreeCharge_eq_original p A h.2.1]
        exact h.2.2.2⟩
  div_iff := isIntDiv_F1_iff_good_bit p
  ordinary := onePart_of_isIntDiv_F1 p

theorem f2Algebra (p : V → Fin 4) : R2Algebra p F2 chi2 (F2Good p) (f2Parity p) where
  chi_bound := chi2_bound
  charge_dvd := fun A hloop hact hthree => twelve_dvd_chi2 p A hact hloop hthree.2 hthree.1
  good_iff := by
    intro A
    constructor
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1, by
        rw [← f2FreeCharge_eq_original p A h.2.1]
        exact h.2.2.2⟩
    · intro h
      exact ⟨h.1, h.2.1, h.2.2.1, by
        rw [f2FreeCharge_eq_original p A h.2.1]
        exact h.2.2.2⟩
  div_iff := isIntDiv_F2_iff_good_bit p
  ordinary := onePart_of_isIntDiv_F2 p

theorem Family.algebra (kind : Family) (p : V → Fin 4) :
    R2Algebra p kind.types kind.matrix (kind.Good p) (kind.parity p) := by
  cases kind
  · exact f1Algebra p
  · exact f2Algebra p

/-- A physical shared refiner, with no refiner or token existence premise. -/
theorem exists_F12_refiner (kind : Family)
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : ∀ a b, G.Adj a b → ∃ k, Link kind.types (p a) (p b) k)
    (ω lam rho : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) 6 (ω * Fintype.card V))
    (hω : ω ≤ 1) (hlam : 0 < lam) (hlamω : 1024 * lam ≤ ω)
    (hrho : 0 < rho) (hscale : (2 ^ 32 : ℝ) * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset)
    (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (indices : Finset TorsionChain.Index) (P : TorsionChain.Index → Finset (Sym2 V))
      (R : Finset (Sym2 V)), R ⊆ G.edgeFinset ∧ Disjoint R X ∧
      RefinerAssembly.RefinesReserve (p := p) (F := kind.types) indices P X R ∧
      (∀ i ∈ indices, P i ⊆ X ∪ R ∧ IsIntDiv p kind.types (P i) ∧ (P i).card ≤ 144) ∧
      DegBounded R (6 * lam * Fintype.card V) ∧
      (indices.card : ℝ) ≤ 2 ^ 23 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ i ∈ indices, incidentLoad (P i) v : ℕ) : ℝ) ≤
        2 ^ 14 * lam * Fintype.card V := by
  refine exists_r2_refiner p kind.types kind.matrix (kind.Good p) (kind.parity p)
    (kind.algebra p) G hG ω lam rho
    (hs.to_ordinaryAntiEdgeful (by norm_num) kind.common)
    hlam (by linarith) (by linarith) hrho hscale hn1 hn2 ?_ ?_ X hXG hX
  · intro B hB S hS
    cases kind
    · exact host_charge_tokens F1 chi1 plus_active_F1 minus_active_F1 plus_charge_F1 minus_charge_F1
        p G S B ω lam rho hs hB hω hlam hlamω hrho hscale hn1 hS
    · exact host_charge_tokens F2 chi2 plus_active_F2 minus_active_F2 plus_charge_F2 minus_charge_F2
        p G S B ω lam rho hs hB hω hlam hlamω hrho hscale hn1 hS
  · intro B hB S hS
    cases kind
    · exact host_torsion_tokens_F1 p G S B ω lam rho hs hB hω hlam hlamω hrho hscale hn1 hS
    · exact host_torsion_tokens_F2 p G S B ω lam rho hs hB hω hlam hlamω hrho hscale hn1 hS

#print axioms f1Algebra
#print axioms f2Algebra
#print axioms exists_F12_refiner

end PaddedF12
