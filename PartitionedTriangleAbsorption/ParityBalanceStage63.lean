/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.LocalCycleTransportStage62
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Algebraic core of the five-root parity/balance certificate

These are coordinate identities and scalar bounds. The global physical
producer with the improved constant is not asserted by this module.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ParityBalanceStage63

open LocalCycleTransportStage62
open scoped BigOperators

def rect {V : Type*} (e : V → V → ℤ) (u v x y : V) : ℤ :=
  e u x - e u y - e v x + e v y

theorem rectangle_identity {V : Type*} (e : V → V → ℤ) (u v x y q : V) :
    rect e u v x y =
      tri e u q x - tri e u q y - tri e v q x + tri e v q y := by
  unfold rect tri
  ring

theorem double_edge_identity {V : Type*} (e : V → V → ℤ) (u v x y : V) :
    2 * (e u x - e v y) =
      tri e u v x - tri e u v y + tri e u x y - tri e v x y := by
  unfold tri
  ring

theorem cycle_rectangles {V I : Type*} [Fintype I]
    (e : V → V → ℤ) (u w z : I → V) (a : V) (σ : Equiv.Perm I) :
    (∑ i, (e (u i) (w i) - e (u (σ i)) (w i))) =
      (∑ i, rect e (u i) (u (σ i)) (w i) (z i)) +
      (∑ i, rect e (u i) a (z i) (z (σ.symm i))) := by
  have hu : (∑ i, e (u i) (z (σ.symm i))) =
      ∑ i, e (u (σ i)) (z i) := by
    simpa using (Equiv.sum_comp σ.symm (fun i => e (u (σ i)) (z i)))
  have ha : (∑ i, e a (z (σ.symm i))) = ∑ i, e a (z i) :=
    Equiv.sum_comp σ.symm (fun i => e a (z i))
  simp only [rect, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hu, ha]
  ring

theorem sign_average (y : ℤ) (hy : y ≠ 0) :
    |y - 1| + |y + 1| = 2 * |y| := by
  by_cases h : 0 ≤ y
  · have h1 : 0 ≤ y - 1 := by omega
    have h2 : 0 ≤ y + 1 := by omega
    rw [abs_of_nonneg h1, abs_of_nonneg h2, abs_of_nonneg h]
    omega
  · have h1 : y - 1 ≤ 0 := by omega
    have h2 : y + 1 ≤ 0 := by omega
    have h3 : y ≤ 0 := by omega
    rw [abs_of_nonpos h1, abs_of_nonpos h2, abs_of_nonpos h3]
    omega

theorem set_budget (m t B Z D : ℤ) (hm : m = 3 * t)
    (hB : B ≤ 4 * t) (hZ : Z ≤ 4 * B) (hD : D ≤ 2 * B) :
    3 * (t + Z + D) ≤ 25 * m := by
  omega

theorem integer_budget (s c B Z D : ℤ)
    (hB : B ≤ c + 2 * s) (hZ : Z ≤ 4 * B) (hD : D ≤ 2 * B) :
    s + Z + D ≤ 13 * s + 6 * c := by
  omega

end PartitionedTriangleAbsorption.ParityBalanceStage63
