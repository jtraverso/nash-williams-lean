/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedDivisibilityCoordinates

/-! # The lattice part of the F1/F2 link dictionary, without cone assumptions -/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegralLinkCoordinates

open Finset TypedApplicationLinks TypedLinkCoefficients TypedDivisibilityCoordinates

theorem F1_coordinates (r : Fin 4) (d : Fin 4 → ℤ) (hn : ∀ j, 0 ≤ d j)
    (hi : LinkLattice F1 r d) :
    ∃ x y z : ℕ, d = demand3 r (first1 r) (second1 r) x y z ∧
      (x + y + z) % 2 = 0 := by
  obtain ⟨a, ha⟩ := hi
  rw [F1_inventory] at ha
  have hn0 : ((d 0).toNat : ℤ) = d 0 := Int.toNat_of_nonneg (hn 0)
  have hn1 : ((d 1).toNat : ℤ) = d 1 := Int.toNat_of_nonneg (hn 1)
  have hn2 : ((d 2).toNat : ℤ) = d 2 := Int.toNat_of_nonneg (hn 2)
  have hn3 : ((d 3).toNat : ℤ) = d 3 := Int.toNat_of_nonneg (hn 3)
  refine ⟨(d r).toNat, (d (first1 r)).toNat, (d (second1 r)).toNat, ?_⟩
  fin_cases r
  all_goals
    repeat rw [sum_insert (by decide)] at ha
    have ha0 := congrFun ha 0
    have ha1 := congrFun ha 1
    have ha2 := congrFun ha 2
    have ha3 := congrFun ha 3
    norm_num [first1, second1, typeDegVec, sum_singleton] at ha0 ha1 ha2 ha3 ⊢
    constructor
    · funext j; fin_cases j <;> simp [demand3, basis, hn0, hn1, hn2, hn3]; omega
    · omega

theorem F2_lower_coordinates (r : Fin 2) (d : Fin 4 → ℤ) (hn : ∀ j, 0 ≤ d j)
    (hi : LinkLattice F2 (lower2 r) d) :
    ∃ x y z : ℕ, d = demand3 (lower2 r) 2 3 x y z ∧ (x + y + z) % 2 = 0 := by
  obtain ⟨a, ha⟩ := hi
  rw [F2_lower_inventory] at ha
  have hn0 : ((d 0).toNat : ℤ) = d 0 := Int.toNat_of_nonneg (hn 0)
  have hn1 : ((d 1).toNat : ℤ) = d 1 := Int.toNat_of_nonneg (hn 1)
  have hn2 : ((d 2).toNat : ℤ) = d 2 := Int.toNat_of_nonneg (hn 2)
  have hn3 : ((d 3).toNat : ℤ) = d 3 := Int.toNat_of_nonneg (hn 3)
  refine ⟨(d (lower2 r)).toNat, (d 2).toNat, (d 3).toNat, ?_⟩
  fin_cases r
  all_goals
    repeat rw [sum_insert (by decide)] at ha
    have ha0 := congrFun ha 0
    have ha1 := congrFun ha 1
    have ha2 := congrFun ha 2
    have ha3 := congrFun ha 3
    norm_num [lower2, typeDegVec, sum_singleton] at ha0 ha1 ha2 ha3 ⊢
    constructor
    · funext j; fin_cases j <;> simp [demand3, basis, hn0, hn1, hn2, hn3]; omega
    · omega

theorem F2_upper_coordinates (r : Fin 2) (d : Fin 4 → ℤ) (hn : ∀ j, 0 ≤ d j)
    (hi : LinkLattice F2 (upper2 r) d) :
    ∃ x y z : ℕ, d = demand3 (central2 r) 0 1 x y z ∧ (x + y + z) % 2 = 0 := by
  obtain ⟨a, ha⟩ := hi
  rw [F2_upper_inventory] at ha
  have hn0 : ((d 0).toNat : ℤ) = d 0 := Int.toNat_of_nonneg (hn 0)
  have hn1 : ((d 1).toNat : ℤ) = d 1 := Int.toNat_of_nonneg (hn 1)
  have hn2 : ((d 2).toNat : ℤ) = d 2 := Int.toNat_of_nonneg (hn 2)
  have hn3 : ((d 3).toNat : ℤ) = d 3 := Int.toNat_of_nonneg (hn 3)
  refine ⟨(d (central2 r)).toNat, (d 0).toNat, (d 1).toNat, ?_⟩
  fin_cases r
  all_goals
    repeat rw [sum_insert (by decide)] at ha
    have ha0 := congrFun ha 0
    have ha1 := congrFun ha 1
    have ha2 := congrFun ha 2
    have ha3 := congrFun ha 3
    norm_num [upper2, central2, typeDegVec, sum_singleton] at ha0 ha1 ha2 ha3 ⊢
    constructor
    · funext j; fin_cases j <;> simp [demand3, basis, hn0, hn1, hn2, hn3]; omega
    · omega

end PartitionedTriangleAbsorption.IntegralLinkCoordinates
