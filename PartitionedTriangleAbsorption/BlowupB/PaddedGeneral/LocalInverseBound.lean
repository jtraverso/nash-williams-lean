/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.LocalInverse

@[expose] public section

/-! Family-dependent complete inverse and its host consumer. This module does
not assert an inverse producer. The established fixed-constant interfaces remain
unchanged; the general producer must supply its own constant. -/

namespace PaddedGeneral

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional

def CompleteInverseCertLocalBound (F : Finset (Multiset (Fin 4))) (C : ℝ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4) (r : Sym2 V → ℝ) (ε γ : ℝ),
    0 ≤ ε → 0 < γ → γ ≤ 1 → 8 ≤ γ * (Fintype.card V : ℝ) →
    (∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i) →
    Sym2DemandSupported p F r → (∀ e, |r e| ≤ ε) → FullSpanCompat p F r →
    ∃ z : TriangleChain V, CopySupported p F (activeCompleteGraph p F) z ∧
      boundary z = r ∧ ∀ T, |z T| ≤ C * ε / (γ ^ 6 * (Fintype.card V : ℝ))

theorem fixed_inverse_to_bound {F : Finset (Multiset (Fin 4))}
    (hI : CompleteInverseCertLocal F) : CompleteInverseCertLocalBound F (2 ^ 20) := hI

def hostInverseConstant (C : ℝ) : ℝ := 18 + 1188 * C

theorem transferred_inverse_bound_general (C ε ω n : ℝ) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : 0 < n) :
    9 * ε / (ω * n / 2) +
        81 * (n ^ 2 * (C * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 2 +
        108 * (n ^ 3 * (C * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 3 ≤
      (hostInverseConstant C / ω ^ 9) * ε / n := by
  have heq : 9 * ε / (ω * n / 2) +
        81 * (n ^ 2 * (C * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 2 +
        108 * (n ^ 3 * (C * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 3 =
      (18 * ω ^ 8 + 324 * C * ω + 864 * C) * ε / (ω ^ 9 * n) := by
    field_simp
    ring
  have hp : ω ^ 8 ≤ 1 := pow_le_one₀ hω.le hω1
  have hc : 18 * ω ^ 8 + 324 * C * ω + 864 * C ≤ hostInverseConstant C := by
    have := mul_le_mul_of_nonneg_left hω1 (show 0 ≤ 324 * C by positivity)
    dsimp [hostInverseConstant]
    linarith
  rw [heq]
  calc
    _ ≤ hostInverseConstant C * ε / (ω ^ 9 * n) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hε) (by positivity)
    _ = _ := by ring

theorem exists_host_chain_inverse_local_bound (F : Finset (Multiset (Fin 4)))
    (C : ℝ) (hC : 0 ≤ C) (hI : CompleteInverseCertLocalBound F C)
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
        |w T| ≤ (hostInverseConstant C / ω ^ 9) * ε / Fintype.card V := by
  classical
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  obtain ⟨z, hzs, hzr, hzb⟩ := hI V p r ε ω hε hω hω1 hlarge hmin hs hr hc
  let M : ℝ := C * ε / (ω ^ 6 * Fintype.card V)
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
  exact (hwb T hT.1.card_eq).trans (transferred_inverse_bound_general C ε ω
    (Fintype.card V) hC hε hω hω1 hnR)

theorem exists_loadDefect_correction_local_bound (F : Finset (Multiset (Fin 4)))
    (C : ℝ) (hC : 0 ≤ C) (hI : CompleteInverseCertLocalBound F C)
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
        |w T| ≤ (hostInverseConstant C / ω ^ 9) * ε / Fintype.card V :=
  exists_host_chain_inverse_local_bound F C hC hI p G (loadDefect p F G φ) ε ω
    hε hω hω1 hlarge hmin hguard (loadDefect_supported p F G φ hactive)
    (loadDefect_zero p F G φ) (loadDefect_bound p F G φ ε hε hloads)
    (loadDefect_fullSpan p F G φ hdiv)

/-- The general error budget that replaces the fixed numerical one. -/
theorem positive_repair_weights_general (C ε ω n φ z : ℝ)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : 0 < n)
    (hlo : ω ^ 2 / n ≤ φ) (hhi : φ ≤ (27 / ω) / n)
    (hz : |z| ≤ (hostInverseConstant C / ω ^ 9) * ε / n)
    (hbudget : (hostInverseConstant C / ω ^ 9) * ε ≤ ω ^ 2 / 2) :
    0 ≤ φ + z ∧ φ + z ≤ (54 / ω) / n :=
  positive_repair_weights ω n φ z hω hω1 hn hlo hhi
    (hz.trans (div_le_div_of_nonneg_right hbudget hn.le))

#print axioms fixed_inverse_to_bound
#print axioms transferred_inverse_bound_general
#print axioms exists_host_chain_inverse_local_bound
#print axioms exists_loadDefect_correction_local_bound
#print axioms positive_repair_weights_general

end PaddedGeneral
