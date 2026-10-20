/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.CompleteCopyInverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.SignedTransfer
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.InverseEstimates

@[expose] public section

/-!
# A bounded signed inverse in the actual F₁/F₂ host

The complete inverse corrects class totals, vertex rows and the zero-row
residual. The transfer theorem places its finite gadgets in the actual host,
coupling contributions on the same unavailable physical edge first.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_host_chain_inverse (p : V → Fin 4)
    (F : Finset (Multiset (Fin 4))) (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Sym2 V → ℝ) (ε ω : ℝ) (hε : 0 ≤ ε) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlarge : 4 ≤ ω * (Fintype.card V : ℝ))
    (hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i)
    (hguard : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 4
      (ω * Fintype.card V / 2))
    (hs : Sym2DemandSupported p F r) (hzero : ∀ e, e ∉ G.edgeFinset → r e = 0)
    (hr : ∀ e, |r e| ≤ ε)
    (hfamily : (F = F1 ∧ F1RealCompatible p (fun a b => r s(a,b))) ∨
      (F = F2 ∧ F2RealCompatible p (fun a b => r s(a,b)))) :
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
  obtain ⟨z, hzs, hzr, hzb⟩ := exists_complete_chain_inverse p F r ε ω
    hε hω hω1 hlarge hmin hs hr hfamily
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

#print axioms exists_host_chain_inverse

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
