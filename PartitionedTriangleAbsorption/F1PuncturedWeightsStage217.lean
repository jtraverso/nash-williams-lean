/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Fractional weights for an ideal balanced F1 level with child edges removed

Each of the four classes has `t` outside and `u` inside vertices. A triangle
with no child vertex has weight `outsideWeight`; one with one child vertex
has weight `boundaryWeight`. Triangles with two child vertices are excluded.

This file proves the scalar identities and near-load bounds, not the graph
counting adapter, a packing, a damaged-host estimate or a cover-down theorem.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1PuncturedWeightsStage217

noncomputable def outsideWeight (t u : ℝ) : ℝ := (t - u) / (2 * t ^ 2)
noncomputable def boundaryWeight (t : ℝ) : ℝ := 1 / (2 * t)

theorem internal_outside_load (t u : ℝ) (ht : 0 < t) :
    2 * t * outsideWeight t u + 2 * u * boundaryWeight t = 1 := by
  unfold outsideWeight boundaryWeight
  field_simp
  nlinarith

theorem internal_boundary_load (t : ℝ) (ht : 0 < t) :
    2 * t * boundaryWeight t = 1 := by
  unfold boundaryWeight
  field_simp

theorem cross_outside_load (t u : ℝ) (ht : 0 < t) :
    2 * (t - 1) * outsideWeight t u + 2 * u * boundaryWeight t =
      1 - (t - u) / t ^ 2 := by
  unfold outsideWeight boundaryWeight
  field_simp
  ring

theorem cross_boundary_load (t : ℝ) (ht : 0 < t) :
    (2 * t - 1) * boundaryWeight t = 1 - 1 / (2 * t) := by
  unfold boundaryWeight
  field_simp

theorem weights_nonnegative (t u : ℝ) (ht : 0 < t) (hu : u ≤ t) :
    0 ≤ outsideWeight t u ∧ 0 ≤ boundaryWeight t := by
  unfold outsideWeight boundaryWeight
  constructor
  · exact div_nonneg (sub_nonneg.mpr hu) (by positivity)
  · positivity

theorem weights_le_four_over_order (t u : ℝ) (ht : 0 < t)
    (hu0 : 0 ≤ u) (hut : u ≤ t) :
    outsideWeight t u ≤ 4 / (4 * (t + u)) ∧
      boundaryWeight t ≤ 4 / (4 * (t + u)) := by
  have htu : 0 < t + u := by linarith
  have hwb : outsideWeight t u ≤ boundaryWeight t := by
    unfold outsideWeight boundaryWeight
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  have hbound : boundaryWeight t ≤ 4 / (4 * (t + u)) := by
    unfold boundaryWeight
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    linarith
  exact ⟨hwb.trans hbound, hbound⟩

theorem cross_loads_near_one (t u : ℝ) (ht : 0 < t)
    (hu0 : 0 ≤ u) (hut : u ≤ t) :
    (1 - 1 / t ≤ 2 * (t - 1) * outsideWeight t u + 2 * u * boundaryWeight t ∧
      2 * (t - 1) * outsideWeight t u + 2 * u * boundaryWeight t ≤ 1) ∧
    (1 - 1 / t ≤ (2 * t - 1) * boundaryWeight t ∧
      (2 * t - 1) * boundaryWeight t ≤ 1) := by
  rw [cross_outside_load t u ht, cross_boundary_load t ht]
  have hd : 0 ≤ (t - u) / t ^ 2 := div_nonneg (by linarith) (by positivity)
  have hdl : (t - u) / t ^ 2 ≤ 1 / t := by
    apply (div_le_div_iff₀ (by positivity) ht).mpr
    nlinarith
  have hb : 0 ≤ 1 / (2 * t) := by positivity
  have hbl : 1 / (2 * t) ≤ 1 / t := by
    apply (div_le_div_iff₀ (by positivity) ht).mpr
    linarith
  constructor <;> constructor <;> linarith

end PartitionedTriangleAbsorption.F1PuncturedWeightsStage217
