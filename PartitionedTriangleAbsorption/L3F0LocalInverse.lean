/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-! # Abstract local inverse (port of `L3F0.LocalInverse.local_inverse`)

Verbatim port of the generic theorem `PartitionedTriangleAbsorption.L3F0.local_inverse` from
`L3_F0_reference/L3F0/LocalInverse.lean`. Only this generic statement is ported; the F0-specific
declarations of that file (and its import `L3F0.LevelBalance`) are not needed here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.L3F0

/-- **Abstract local inverse.** -/
theorem local_inverse {E T : Type*} [Fintype E] [Fintype T]
    (Λ : (T → ℝ) →ₗ[ℝ] (E → ℝ)) (C : (E → ℝ) →ₗ[ℝ] (T → ℝ)) (K : Submodule ℝ (E → ℝ))
    (S : Submodule ℝ (T → ℝ)) (hK : ∀ d ∈ K, d - Λ (C d) ∈ K) (hCS : ∀ d ∈ K, C d ∈ S)
    {κ c : ℝ} (hκ : κ < 1) (hc : 0 ≤ c)
    (hres : ∀ d ∈ K, ‖d - Λ (C d)‖ ≤ κ * ‖d‖) (hC : ∀ d ∈ K, ‖C d‖ ≤ c * ‖d‖) :
    ∀ d ∈ K, ∃ x ∈ S, Λ x = d ∧ ‖x‖ ≤ c / (1 - κ) * ‖d‖ := by
  have hΛK : ∀ d ∈ K, Λ (C d) ∈ K := by
    intro d hd
    have := K.sub_mem hd (hK d hd)
    simpa using this
  let f : K →ₗ[ℝ] K :=
    { toFun := fun d => ⟨Λ (C d), hΛK d d.2⟩
      map_add' := fun a b => by ext1; simp
      map_smul' := fun r a => by ext1; simp }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro d hd
    have h0 : Λ (C d) = 0 := congrArg Subtype.val hd
    have := hres d d.2
    rw [h0, sub_zero] at this
    have hn : ‖(d : E → ℝ)‖ = 0 := by
      have := norm_nonneg (d : E → ℝ)
      nlinarith
    ext1; simpa using hn
  have hsurj : Function.Surjective f := LinearMap.injective_iff_surjective.mp hinj
  intro d hd
  obtain ⟨d', hd'⟩ := hsurj ⟨d, hd⟩
  have hΛ : Λ (C d') = d := congrArg Subtype.val hd'
  refine ⟨C d', hCS d' d'.2, hΛ, ?_⟩
  have h1 : ‖(d' : E → ℝ)‖ ≤ ‖d‖ + κ * ‖(d' : E → ℝ)‖ := by
    have := hres d' d'.2
    rw [hΛ] at this
    calc ‖(d' : E → ℝ)‖ = ‖d + ((d' : E → ℝ) - d)‖ := by congr 1; abel
      _ ≤ ‖d‖ + ‖(d' : E → ℝ) - d‖ := norm_add_le _ _
      _ ≤ ‖d‖ + κ * ‖(d' : E → ℝ)‖ := by linarith
  have h1' : ‖(d' : E → ℝ)‖ ≤ ‖d‖ / (1 - κ) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  calc ‖C d'‖ ≤ c * ‖(d' : E → ℝ)‖ := hC d' d'.2
    _ ≤ c * (‖d‖ / (1 - κ)) := mul_le_mul_of_nonneg_left h1' hc
    _ = c / (1 - κ) * ‖d‖ := by ring

end PartitionedTriangleAbsorption.L3F0
