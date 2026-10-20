/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedGeneral.RealInverse.Basic

@[expose] public section

/-! # Exact loads and profiles of the typed edge and vertex modes

* `load_edgeMode`: for a symmetric, diagonal-zero edge function with zero rows
  into every class, the typed weight `χ_τ (h ab + h ac + h bc)` has edge load
  `h xy * edgeFactor τ (p x) (p y)`.
* `classRow_vertexMode`: for a vertex function with zero sum on every class,
  the typed weight `χ_τ (φ a + φ b + φ c)` has local profile
  `φ u * vertexFactor τ (p u) l` at every vertex `u`. -/

noncomputable section

namespace PaddedGeneral.RealInverse

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Real indicator of equality of two labels. -/
def ind (a b : Fin 4) : ℝ := if a = b then 1 else 0

/-- The edge-mode multiplier: `n_z - 2[i = z] - 2[j = z]` for the completing label `z`. -/
def edgeFactor (n : Fin 4 → ℝ) (τ : Multiset (Fin 4)) (i j : Fin 4) : ℝ :=
  ∑ z : Fin 4, if ({i, j, z} : Multiset (Fin 4)) = τ then
    n z - 2 * ind i z - 2 * ind j z else 0

/-- The vertex-mode multiplier of the local profile in class `l` at a root of class `i`. -/
def vertexFactor (n : Fin 4 → ℝ) (τ : Multiset (Fin 4)) (i l : Fin 4) : ℝ :=
  ∑ z : Fin 4, if ({i, l, z} : Multiset (Fin 4)) = τ then
    (n l - 2 * ind i l) * (n z - ind i z - ind l z) - ind i z * (n l - ind i l) +
      ind l z * ind i l else 0

omit [DecidableEq V] in
theorem sum_classVertices_one (p : V → Fin 4) (z : Fin 4) :
    (∑ _c ∈ classVertices p z, (1 : ℝ)) = classSize p z := by
  simp [classSize]

theorem load_edgeMode (p : V → Fin 4) (τ : Multiset (Fin 4)) (h : V → V → ℝ)
    (hs : ∀ a b, h a b = h b a) (hd : ∀ a, h a a = 0)
    (hr : ∀ a l, ∑ c ∈ classVertices p l, h a c = 0) {x y : V} (hxy : x ≠ y) :
    ternaryLoad (fun a b c => chi p τ a b c * (h a b + h a c + h b c)) x y =
      h x y * edgeFactor (classSize p) τ (p x) (p y) := by
  have e : ternaryLoad (fun a b c => chi p τ a b c * (h a b + h a c + h b c)) x y =
      h x y * (∑ c, chi p τ x y c * 1) + (∑ c, chi p τ x y c * h x c) +
        ∑ c, chi p τ x y c * h y c := by
    unfold ternaryLoad
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro c _
    ring
  rw [e, sum_chi_mul p τ hxy, sum_chi_mul p τ hxy, sum_chi_mul p τ hxy, edgeFactor,
    mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro z _
  rw [hr x z, hr y z, hd x, hd y, hs y x, sum_classVertices_one]
  unfold ind
  split_ifs <;> ring

theorem load_vertexMode (p : V → Fin 4) (τ : Multiset (Fin 4)) (φ : V → ℝ)
    (hφ : ∀ l, ∑ c ∈ classVertices p l, φ c = 0) (u y : V) :
    ternaryLoad (fun a b c => chi p τ a b c * (φ a + φ b + φ c)) u y =
      if y ≠ u then ∑ z : Fin 4, if ({p u, p y, z} : Multiset (Fin 4)) = τ then
        (classSize p z - ind (p u) z - ind (p y) z - ind (p u) z) * φ u +
          (classSize p z - ind (p u) z - ind (p y) z - ind (p y) z) * φ y else 0
      else 0 := by
  by_cases hyu : y = u
  · subst y
    rw [if_neg (not_not.mpr rfl)]
    unfold ternaryLoad
    exact sum_eq_zero fun c _ => by
      show chi p τ u u c * _ = 0
      rw [chi_self12, zero_mul]
  · rw [if_pos hyu]
    have hxy : u ≠ y := Ne.symm hyu
    have e : ternaryLoad (fun a b c => chi p τ a b c * (φ a + φ b + φ c)) u y =
        (φ u + φ y) * (∑ c, chi p τ u y c * 1) + ∑ c, chi p τ u y c * φ c := by
      unfold ternaryLoad
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro c _
      ring
    rw [e, sum_chi_mul p τ hxy, sum_chi_mul p τ hxy, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro z _
    rw [hφ z, sum_classVertices_one]
    unfold ind
    split_ifs <;> ring

theorem classRow_vertexMode (p : V → Fin 4) (τ : Multiset (Fin 4)) (φ : V → ℝ)
    (hφ : ∀ l, ∑ c ∈ classVertices p l, φ c = 0) (u : V) (l : Fin 4) :
    classRow p (fun a b => ternaryLoad (fun a b c => chi p τ a b c * (φ a + φ b + φ c)) a b)
      u l = φ u * vertexFactor (classSize p) τ (p u) l := by
  unfold classRow
  have hstep : ∀ y ∈ classVertices p l,
      ternaryLoad (fun a b c => chi p τ a b c * (φ a + φ b + φ c)) u y =
        ∑ z : Fin 4, if ({p u, l, z} : Multiset (Fin 4)) = τ then
          (if y ≠ u then (classSize p z - ind (p u) z - ind l z - ind (p u) z) * φ u +
            (classSize p z - ind (p u) z - ind l z - ind l z) * φ y else 0) else 0 := by
    intro y hy
    have hpy : p y = l := (mem_classVertices p l y).mp hy
    rw [load_vertexMode p τ φ hφ u y, hpy]
    by_cases hyu : y ≠ u
    · rw [if_pos hyu]
      refine sum_congr rfl fun z _ => ?_
      by_cases hz : ({p u, l, z} : Multiset (Fin 4)) = τ
      · rw [if_pos hz, if_pos hz, if_pos hyu]
      · rw [if_neg hz, if_neg hz]
    · rw [if_neg hyu]
      symm
      refine sum_eq_zero fun z _ => ?_
      rw [if_neg hyu, ite_self]
  rw [sum_congr rfl hstep, sum_comm, vertexFactor, mul_sum]
  apply sum_congr rfl
  intro z _
  split_ifs with hz
  · rw [sum_avoid_one, sum_add_distrib, ← mul_sum _ φ, hφ l]
    simp only [sum_const, nsmul_eq_mul]
    rw [show ((classVertices p l).card : ℝ) = classSize p l from rfl]
    have hu : (u ∈ classVertices p l) ↔ p u = l := mem_classVertices p l u
    by_cases hul : p u = l
    · rw [if_pos (hu.mpr hul)]
      subst hul
      unfold ind
      simp only [↓reduceIte]
      split_ifs <;> ring
    · rw [if_neg (fun h => hul (hu.mp h))]
      unfold ind
      split_ifs <;> ring
  · simp

end PaddedGeneral.RealInverse
