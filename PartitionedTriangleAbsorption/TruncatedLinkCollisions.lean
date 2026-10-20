/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BernoulliExposure

/-! # The effect of two endpoint changes on truncated link conflicts

The clipped pair-count is the real-valued version of `choose (min degree cap) 2`.
Adding one link edge changes two endpoint degrees; each endpoint contributes
at most `cap`. This supplies the coordinate bound before any concentration
argument, rather than assuming the untruncated collision count is Lipschitz.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TruncatedLinkCollisions

noncomputable def clippedPairs (cap degree : ℕ) : ℝ :=
  (min degree cap : ℕ) * ((min degree cap : ℕ) - (1 : ℝ)) / 2

theorem clippedPairs_succ_bounds (cap degree : ℕ) :
    0 ≤ clippedPairs cap (degree + 1) - clippedPairs cap degree ∧
      clippedPairs cap (degree + 1) - clippedPairs cap degree ≤ (cap : ℝ) := by
  by_cases h : degree < cap
  · have hd : degree ≤ cap := Nat.le_of_lt h
    have hs : degree + 1 ≤ cap := h
    simp only [clippedPairs, Nat.min_eq_left hd, Nat.min_eq_left hs,
      Nat.cast_add, Nat.cast_one]
    have hdR : (degree : ℝ) ≤ (cap : ℝ) := by exact_mod_cast hd
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) degree]
  · have hd : cap ≤ degree := Nat.le_of_not_gt h
    have hs : cap ≤ degree + 1 := hd.trans (Nat.le_succ degree)
    simp only [clippedPairs, Nat.min_eq_right hd, Nat.min_eq_right hs, sub_self]
    exact ⟨le_rfl, Nat.cast_nonneg cap⟩

theorem two_endpoint_increment_bound (cap first second : ℕ) :
    |(clippedPairs cap (first + 1) + clippedPairs cap (second + 1)) -
      (clippedPairs cap first + clippedPairs cap second)| ≤ 2 * (cap : ℝ) := by
  obtain ⟨hfirst0, hfirst⟩ := clippedPairs_succ_bounds cap first
  obtain ⟨hsecond0, hsecond⟩ := clippedPairs_succ_bounds cap second
  rw [abs_le]
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) cap]

end PartitionedTriangleAbsorption.TruncatedLinkCollisions
