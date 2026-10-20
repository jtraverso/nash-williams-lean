/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ParityBalanceStage63
public import Mathlib.Algebra.Order.Ring.Abs

/-! # Integer star and tetrahedron systems for structural certificates

These algebraic lemmas do not assert the global physical producer. Its
anchoring, finite-sum accounting and physical support are separate obligations.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ClassLatticeStage65

open LocalCycleTransportStage62

theorem star_difference {V : Type*} (e : V → V → ℤ) (v a b c : V) :
    tri e v b c - tri e a b c = e v b + e v c - e a b - e a c := by
  unfold tri
  ring

theorem star_coefficients (d₀ d₁ d₂ s : ℤ) (hs : d₀ + d₁ + d₂ = 2 * s) :
    (s - d₂) + (s - d₁) = d₀ ∧
    (s - d₂) + (s - d₀) = d₁ ∧
    (s - d₁) + (s - d₀) = d₂ := by omega

theorem pair_abs_bound (a b c q : ℤ) (hq : 2 * q = a + b - c) :
    2 * |q| ≤ |a| + |b| + |c| := by
  calc 2 * |q| = |2 * q| := by rw [abs_mul]; norm_num
    _ = |a + b - c| := congrArg abs hq
    _ ≤ |a + b| + |c| := by
      simpa [sub_eq_add_neg] using abs_add_le (a + b) (-c)
    _ ≤ |a| + |b| + |c| := by have := abs_add_le a b; omega

theorem star_budget (d₀ d₁ d₂ s : ℤ) (hs : d₀ + d₁ + d₂ = 2 * s) :
    2 * (|s - d₂| + |s - d₁| + |s - d₀|) ≤
      3 * (|d₀| + |d₁| + |d₂|) := by
  have h₀ := pair_abs_bound d₀ d₁ d₂ (s - d₂) (by omega)
  have h₁ := pair_abs_bound d₀ d₂ d₁ (s - d₁) (by omega)
  have h₂ := pair_abs_bound d₁ d₂ d₀ (s - d₀) (by omega)
  omega

theorem tetrahedron_inverse (x₀₁ x₀₂ x₀₃ x₁₂ x₁₃ x₂₃ a b c d : ℤ)
    (h₀₁ : x₀₁ = a + b) (h₀₂ : x₀₂ = a + c) (h₀₃ : x₀₃ = b + c)
    (h₁₂ : x₁₂ = a + d) (h₁₃ : x₁₃ = b + d) (_h₂₃ : x₂₃ = c + d) :
    2 * a = x₀₁ + x₀₂ - x₀₃ ∧ 2 * b = x₀₁ + x₀₃ - x₀₂ ∧
    2 * c = x₀₂ + x₀₃ - x₀₁ ∧ 2 * d = x₁₂ + x₁₃ - x₀₁ := by omega

theorem tetrahedron_budget (x₀₁ x₀₂ x₀₃ x₁₂ x₁₃ x₂₃ a b c d : ℤ)
    (h₀₁ : x₀₁ = a + b) (h₀₂ : x₀₂ = a + c) (h₀₃ : x₀₃ = b + c)
    (h₁₂ : x₁₂ = a + d) (h₁₃ : x₁₃ = b + d) (h₂₃ : x₂₃ = c + d) :
    |a| + |b| + |c| + |d| ≤
      2 * (|x₀₁| + |x₀₂| + |x₀₃| + |x₁₂| + |x₁₃| + |x₂₃|) := by
  obtain ⟨ha, hb, hc, hd⟩ :=
    tetrahedron_inverse x₀₁ x₀₂ x₀₃ x₁₂ x₁₃ x₂₃ a b c d h₀₁ h₀₂ h₀₃ h₁₂ h₁₃ h₂₃
  have h₀ := pair_abs_bound x₀₁ x₀₂ x₀₃ a ha
  have h₁ := pair_abs_bound x₀₁ x₀₃ x₀₂ b hb
  have h₂ := pair_abs_bound x₀₂ x₀₃ x₀₁ c hc
  have h₃ := pair_abs_bound x₁₂ x₁₃ x₀₁ d hd
  have := abs_nonneg x₀₁
  have := abs_nonneg x₀₂
  have := abs_nonneg x₀₃
  have := abs_nonneg x₁₂
  have := abs_nonneg x₁₃
  have := abs_nonneg x₂₃
  omega

end PartitionedTriangleAbsorption.ClassLatticeStage65
