/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.HostGap

@[expose] public section

set_option exponentiation.threshold 512

/-! # Concrete polynomial scales for padded F1/F2 absorption -/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

noncomputable def paddedKappa (ω : ℝ) : ℝ := ω ^ 12 / 2 ^ 60

noncomputable def paddedAbsDelta (ω : ℝ) : ℝ := paddedKappa ω / 8

noncomputable def paddedRho (ω : ℝ) : ℝ := ω ^ 26 / 2 ^ 262

theorem paddedKappa_pos {ω : ℝ} (hω : 0 < ω) : 0 < paddedKappa ω := by
  unfold paddedKappa
  positivity

theorem paddedAbsDelta_pos {ω : ℝ} (hω : 0 < ω) : 0 < paddedAbsDelta ω :=
  div_pos (paddedKappa_pos hω) (by norm_num)

theorem paddedRho_pos {ω : ℝ} (hω : 0 < ω) : 0 < paddedRho ω := by
  unfold paddedRho
  positivity

theorem padded_delta_small {ω : ℝ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) :
    64 * ((2 ^ 21 : ℝ) + 1) * paddedAbsDelta ω ≤ ω := by
  have hpow : ω ^ 12 ≤ ω := pow_le_of_le_one hω hω1 (by decide)
  unfold paddedAbsDelta paddedKappa
  norm_num
  linarith

theorem paddedRho_le_refiner {ω : ℝ} (hω : 0 ≤ ω) :
    paddedRho ω ≤ refinerRho (2 ^ 21) ω (paddedAbsDelta ω) := by
  unfold paddedRho refinerRho refinerLambda paddedAbsDelta paddedKappa
  ring_nf
  nlinarith only [pow_nonneg hω 26]

theorem paddedRho_le_absDelta {ω : ℝ} (hω : 0 ≤ ω) (hω1 : ω ≤ 1) :
    paddedRho ω ≤ paddedAbsDelta ω := by
  have hpow : ω ^ 26 ≤ ω ^ 12 := pow_le_pow_of_le_one hω hω1 (by decide)
  have hnonneg : 0 ≤ ω ^ 12 := pow_nonneg hω _
  unfold paddedRho paddedAbsDelta paddedKappa
  norm_num
  linarith

/-- The physical inverse constant 2^32/ω^9 fits inside a quarter of the lower weight. -/
theorem padded_repair_budget {ω : ℝ} (hω : 0 < ω) :
    ((2 ^ 32 : ℝ) / ω ^ 9) * (2 * (27 / ω) * paddedKappa ω) ≤ ω ^ 2 / 4 := by
  have heq : ((2 ^ 32 : ℝ) / ω ^ 9) * (2 * (27 / ω) * paddedKappa ω) =
      (54 / 2 ^ 28 : ℝ) * ω ^ 2 := by
    unfold paddedKappa
    field_simp
    ring
  rw [heq]
  norm_num
  nlinarith only [sq_nonneg ω]

theorem universalAbsorbers_mono_rho {V : Type*} [Fintype V] [DecidableEq V]
    {t : ℕ} (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] {ρ ρ' δ : ℝ}
    (h : UniversalAbsorbers p F G ρ δ) (hρ : ρ' ≤ ρ) :
    UniversalAbsorbers p F G ρ' δ := by
  intro X hX hdeg
  apply h X hX
  intro v
  exact (hdeg v).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hρ (by norm_num)) (Nat.cast_nonneg _))

theorem Family.universal_simple (kind : Family)
    {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω : ℝ)
    (hG : ∀ u v, G.Adj u v → ∃ k, Link kind.types (p u) (p v) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) (2 ^ 21)
      (ω * Fintype.card V))
    (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 1 ≤ paddedRho ω * Fintype.card V) :
    UniversalAbsorbers p kind.types G (paddedRho ω) (paddedAbsDelta ω) := by
  obtain ⟨S, C, hS, hC, _, _, hmain⟩ := universal_F12_uniform kind
  subst S C
  have hsmall : 64 * ((((2 ^ 21 : ℕ) : ℝ)) + 1) * paddedAbsDelta ω ≤ ω := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using padded_delta_small hω.le hω1
  have hρ : paddedRho ω ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using paddedRho_le_refiner hω.le
  have hn' : 1 ≤ refinerRho (((2 ^ 21 : ℕ) : ℝ)) ω (paddedAbsDelta ω) *
      Fintype.card V := hn.trans (mul_le_mul_of_nonneg_right hρ (Nat.cast_nonneg _))
  exact universalAbsorbers_mono_rho p kind.types G
    (hmain p G ω (paddedAbsDelta ω) hG hs hω hω1 (paddedAbsDelta_pos hω) hsmall hn') hρ

theorem Family.universal_of_padded (kind : Family)
    {V : Type*} [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (J : Finset (Sym2 V)) (hloop : ∀ e ∈ J, ¬ e.IsDiag) (ω : ℝ) (K : ℕ)
    (hK : (2 ^ 21 : ℕ) + 1 ≤ K)
    (hallowed : ∀ u v, s(u, v) ∈ J → PaddedInputs.AllowedPair kind.types (p u) (p v))
    (hext : PaddedInputs.ExtendableT K p kind.types J ω)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : 1 ≤ paddedRho ω * Fintype.card V) :
    UniversalAbsorbers p kind.types (PaddedInputs.edgeGraph J)
      (paddedRho ω) (paddedAbsDelta ω) :=
  kind.universal_simple p (PaddedInputs.edgeGraph J) ω
    (PaddedInputs.edgeGraph_allowed p kind.types J hallowed)
    (PaddedInputs.guardedSupply_of_padded p kind.types J hloop ω (2 ^ 21) hK hext)
    hω hω1 hn

#print axioms paddedRho_le_refiner
#print axioms padded_repair_budget
#print axioms Family.universal_of_padded

end PaddedF12
