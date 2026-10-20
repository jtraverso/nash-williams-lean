/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite-dimensional exact repair of a linear approximate right inverse

This module proves the linear-algebra step used after restricting the explicit
mixed-triangle inverse from a host with all crossing edges to the actual host.
It does not assume, or assert, that the required graph-specific approximate
inverse has already been constructed.

The error contracts by at most one half. The resulting endomorphism of the
finite-dimensional demand space is injective and hence surjective. This gives
an exact right inverse with twice the norm bound, without an infinite series.
-/

namespace PartitionedTriangleAbsorption.F0Direct.LinearRepair

variable {E W : Type*}
  [NormedAddCommGroup E] [Module ℝ E]
  [NormedAddCommGroup W] [Module ℝ W]

/-- A half-error estimate controls the norm of every preimage. -/
theorem norm_le_two_mul_norm_of_half_error (B : E →ₗ[ℝ] E)
    (herror : ∀ x : E, ‖x - B x‖ ≤ (1 / 2 : ℝ) * ‖x‖) (x : E) :
    ‖x‖ ≤ 2 * ‖B x‖ := by
  have htriangle := norm_add_le (x - B x) (B x)
  rw [sub_add_cancel] at htriangle
  have h := herror x
  linarith

/-- An endomorphism whose difference from the identity has norm at most one
half is injective. No completeness or continuity assumption is needed. -/
theorem injective_of_half_error (B : E →ₗ[ℝ] E)
    (herror : ∀ x : E, ‖x - B x‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    Function.Injective B := by
  intro x y hxy
  have h := norm_le_two_mul_norm_of_half_error B herror (x - y)
  have hzero : B (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  rw [hzero, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- Finite-dimensional exact repair, with the quantitative coefficient bound.
`E` can be the subspace of supported balanced physical edge demands and `W`
the space of real functions on the actual mixed copies. -/
theorem exact_repair_of_half_error [FiniteDimensional ℝ E]
    (boundary : W →ₗ[ℝ] E) (T : E →ₗ[ℝ] W) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : E, ‖T x‖ ≤ C * ‖x‖)
    (herror : ∀ x : E, ‖x - boundary (T x)‖ ≤ (1 / 2 : ℝ) * ‖x‖)
    (g : E) :
    ∃ w : W, boundary w = g ∧ ‖w‖ ≤ (2 * C) * ‖g‖ := by
  let B : E →ₗ[ℝ] E := boundary.comp T
  have hB : ∀ x : E, ‖x - B x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := herror
  have hsurj : Function.Surjective B :=
    LinearMap.surjective_of_injective (injective_of_half_error B hB)
  obtain ⟨y, hy⟩ := hsurj g
  refine ⟨T y, hy, ?_⟩
  have hybound := norm_le_two_mul_norm_of_half_error B hB y
  rw [hy] at hybound
  calc
    ‖T y‖ ≤ C * ‖y‖ := hbound y
    _ ≤ C * (2 * ‖g‖) := mul_le_mul_of_nonneg_left hybound hC
    _ = (2 * C) * ‖g‖ := by ring

/-- The repaired right inverse can itself be chosen as one linear map. -/
theorem exists_linear_rightInverse_of_half_error [FiniteDimensional ℝ E]
    (boundary : W →ₗ[ℝ] E) (T : E →ₗ[ℝ] W) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ x : E, ‖T x‖ ≤ C * ‖x‖)
    (herror : ∀ x : E, ‖x - boundary (T x)‖ ≤ (1 / 2 : ℝ) * ‖x‖) :
    ∃ S : E →ₗ[ℝ] W, (∀ g : E, boundary (S g) = g) ∧
      ∀ g : E, ‖S g‖ ≤ (2 * C) * ‖g‖ := by
  let B : E →ₗ[ℝ] E := boundary.comp T
  have hB : ∀ x : E, ‖x - B x‖ ≤ (1 / 2 : ℝ) * ‖x‖ := herror
  have hinj : Function.Injective B := injective_of_half_error B hB
  let iso : E ≃ₗ[ℝ] E :=
    LinearEquiv.ofBijective B ⟨hinj, LinearMap.surjective_of_injective hinj⟩
  refine ⟨T.comp iso.symm.toLinearMap, ?_, ?_⟩
  · intro g
    exact iso.apply_symm_apply g
  · intro g
    change ‖T (iso.symm g)‖ ≤ (2 * C) * ‖g‖
    have hybound := norm_le_two_mul_norm_of_half_error B hB (iso.symm g)
    have hy : B (iso.symm g) = g := iso.apply_symm_apply g
    rw [hy] at hybound
    calc
      ‖T (iso.symm g)‖ ≤ C * ‖iso.symm g‖ := hbound _
      _ ≤ C * (2 * ‖g‖) := mul_le_mul_of_nonneg_left hybound hC
      _ = (2 * C) * ‖g‖ := by ring

#print axioms norm_le_two_mul_norm_of_half_error
#print axioms injective_of_half_error
#print axioms exact_repair_of_half_error
#print axioms exists_linear_rightInverse_of_half_error

end PartitionedTriangleAbsorption.F0Direct.LinearRepair
