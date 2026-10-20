/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Ring.Parity

/-! # Exact nonnegative coefficient tests for the typed vertex links

These are universal arithmetic equivalences, not finite searches and not
global graph decompositions. The three systems are identified with the
actual F0--F3 link generators in a separate module.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLinkArithmetic

def Wedge (x y : ℕ) : Prop := ∃ a b : ℕ, x = a ∧ y = a + 2 * b

def Triangle (x y z : ℕ) : Prop :=
  ∃ a b c : ℕ, x = a + b ∧ y = a + c ∧ z = b + c

def Fork (x y z : ℕ) : Prop :=
  ∃ a b c d : ℕ, x = a + b ∧ y = a + 2 * c ∧ z = b + 2 * d

theorem wedge_iff (x y : ℕ) : Wedge x y ↔ x ≤ y ∧ (x + y) % 2 = 0 := by
  constructor
  · rintro ⟨a, b, rfl, rfl⟩
    omega
  · rintro ⟨hxy, heven⟩
    exact ⟨x, (y - x) / 2, rfl, by omega⟩

theorem triangle_iff (x y z : ℕ) :
    Triangle x y z ↔ x ≤ y + z ∧ y ≤ x + z ∧ z ≤ x + y ∧ (x + y + z) % 2 = 0 := by
  constructor
  · rintro ⟨a, b, c, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hx, hy, hz, heven⟩
    refine ⟨(x + y - z) / 2, (x + z - y) / 2, (y + z - x) / 2, ?_⟩
    omega

theorem fork_iff (x y z : ℕ) :
    Fork x y z ↔ x ≤ y + z ∧ (x + y + z) % 2 = 0 ∧ (0 < x ∨ y % 2 = 0) := by
  constructor
  · rintro ⟨a, b, c, d, rfl, rfl, rfl⟩
    omega
  · rintro ⟨hcone, heven, hboundary⟩
    by_cases hy : y ≤ x
    · exact ⟨y, x - y, 0, (z - (x - y)) / 2, by omega⟩
    · by_cases hp : (y - x) % 2 = 0
      · exact ⟨x, 0, (y - x) / 2, z / 2, by omega⟩
      · exact ⟨x - 1, 1, (y - (x - 1)) / 2, (z - 1) / 2, by omega⟩

/-- All holes, for every size: not merely those inside a bounded test box. -/
theorem fork_hole_iff (x y z : ℕ) (hcone : x ≤ y + z)
    (heven : (x + y + z) % 2 = 0) :
    ¬ Fork x y z ↔ x = 0 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
  rw [fork_iff]
  omega

/-- One allowed central-to-branch pair repairs every arithmetic hole. -/
theorem fork_after_one_pair (x y z : ℕ) (hcone : x ≤ y + z)
    (heven : (x + y + z) % 2 = 0) : Fork (x + 1) (y + 1) z := by
  rw [fork_iff]
  omega

/-- Adding pairs entirely within a branch cannot fix the missing central coordinate. -/
theorem fork_bad_correction (u v k : ℕ) : ¬ Fork 0 (2 * u + 1 + 2 * k) (2 * v + 1) := by
  rw [fork_iff]
  omega

end PartitionedTriangleAbsorption.TypedLinkArithmetic
