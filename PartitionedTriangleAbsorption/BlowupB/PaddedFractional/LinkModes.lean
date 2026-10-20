/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.CompleteModes

/-!
# The two link systems appearing in F₁ and F₂

After renaming vertices, each link is either the triangle, or has edges
`ab, ac, bb, cc`. The displayed solutions are linear, have operator norm
at most two in the maximum norm, and preserve zero sums across a class.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

theorem star_loop_link_solution (x y z : ℝ) :
    x + 0 = x ∧ x + 2 * ((y - x) / 2) = y ∧ 0 + 2 * (z / 2) = z := by
  constructor
  · ring
  constructor <;> ring

theorem triangle_link_solution (x y z : ℝ) :
    (x + y - z) / 2 + (x + z - y) / 2 = x ∧
    (x + y - z) / 2 + (y + z - x) / 2 = y ∧
    (x + z - y) / 2 + (y + z - x) / 2 = z := by
  constructor
  · ring
  constructor <;> ring

theorem star_loop_link_bound (x y z D : ℝ)
    (hx : |x| ≤ D) (hy : |y| ≤ D) (hz : |z| ≤ D) :
    |x| ≤ D ∧ |(0 : ℝ)| ≤ D ∧ |(y - x) / 2| ≤ D ∧ |z / 2| ≤ D := by
  have hD := (abs_nonneg x).trans hx
  rw [abs_le] at hx hy hz
  refine ⟨abs_le.mpr hx, by simpa using hD, ?_, ?_⟩ <;>
    rw [abs_le] <;> constructor <;> linarith

theorem triangle_link_bound (x y z D : ℝ)
    (hx : |x| ≤ D) (hy : |y| ≤ D) (hz : |z| ≤ D) :
    |(x + y - z) / 2| ≤ 2 * D ∧
    |(x + z - y) / 2| ≤ 2 * D ∧
    |(y + z - x) / 2| ≤ 2 * D := by
  have hD := (abs_nonneg x).trans hx
  rw [abs_le] at hx hy hz
  refine ⟨?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

variable {V : Type*} [Fintype V]

theorem star_loop_link_zero_sums (x y z : V → ℝ)
    (hx : ∑ v, x v = 0) (hy : ∑ v, y v = 0) (hz : ∑ v, z v = 0) :
    (∑ v, x v) = 0 ∧
    (∑ v, (y v - x v) / 2) = 0 ∧ (∑ v, z v / 2) = 0 := by
  simp only [← sum_div, sum_sub_distrib, hx, hy, hz, sub_self, zero_div, and_self]

theorem triangle_link_zero_sums (x y z : V → ℝ)
    (hx : ∑ v, x v = 0) (hy : ∑ v, y v = 0) (hz : ∑ v, z v = 0) :
    (∑ v, (x v + y v - z v) / 2) = 0 ∧
    (∑ v, (x v + z v - y v) / 2) = 0 ∧
    (∑ v, (y v + z v - x v) / 2) = 0 := by
  simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hx, hy, hz,
    add_zero, sub_self, zero_div, and_self]

#print axioms star_loop_link_solution
#print axioms triangle_link_solution
#print axioms star_loop_link_bound
#print axioms triangle_link_bound
#print axioms star_loop_link_zero_sums
#print axioms triangle_link_zero_sums

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
