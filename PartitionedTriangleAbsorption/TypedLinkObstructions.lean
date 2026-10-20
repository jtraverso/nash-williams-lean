/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Converse certificates and genuine holes for the actual typed families -/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedApplicationLinks

open TypedLinkArithmetic TypedLinkCoefficients

theorem F0_wedge_of_coefficients (r : Fin 2) (x y : ℕ)
    (h : Realizable F0 r (demand2 r (other0 r) x y)) : Wedge x y := by
  obtain ⟨c, h⟩ := h
  rw [F0_inventory] at h
  refine ⟨c {r, r, other0 r}, c {r, other0 r, other0 r}, ?_⟩
  fin_cases r <;> (repeat rw [Finset.sum_insert (by decide)] at h)
  all_goals
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    norm_num [other0, demand2, basis, typeDegVec, Finset.sum_singleton] at h0 h1 ⊢
    omega

theorem F2_lower_triangle_of_coefficients (r : Fin 2) (x y z : ℕ)
    (h : Realizable F2 (lower2 r) (demand3 (lower2 r) 2 3 x y z)) :
    Triangle x y z := by
  obtain ⟨c, h⟩ := h
  rw [F2_lower_inventory] at h
  refine ⟨c {lower2 r, lower2 r, 2}, c {lower2 r, lower2 r, 3}, c {lower2 r, 2, 3}, ?_⟩
  fin_cases r <;> (repeat rw [Finset.sum_insert (by decide)] at h)
  all_goals
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    norm_num [lower2, demand3, basis, typeDegVec, Finset.sum_singleton] at h0 h1 h2 h3 ⊢
    omega

theorem F3_triangle_of_coefficients (r : Fin 4) (x y z : ℕ)
    (h : Realizable F3 r (demand3 (others3 r 0) (others3 r 1) (others3 r 2) x y z)) :
    Triangle x y z := by
  obtain ⟨c, h⟩ := h
  rw [F3_inventory] at h
  refine ⟨c {r, others3 r 0, others3 r 1}, c {r, others3 r 0, others3 r 2},
    c {r, others3 r 1, others3 r 2}, ?_⟩
  fin_cases r <;> (repeat rw [Finset.sum_insert (by decide)] at h)
  all_goals
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    norm_num [others3, demand3, basis, typeDegVec, Finset.sum_singleton] at h0 h1 h2 h3 ⊢
    omega

theorem F1_fork_of_coefficients (r : Fin 4) (x y z : ℕ)
    (h : Realizable F1 r (demand3 r (first1 r) (second1 r) x y z)) :
    Fork x y z := by
  obtain ⟨c, h⟩ := h
  rw [F1_inventory] at h
  refine ⟨c {r, r, first1 r}, c {r, r, second1 r},
    c {r, first1 r, first1 r}, c {r, second1 r, second1 r}, ?_⟩
  fin_cases r <;> (repeat rw [Finset.sum_insert (by decide)] at h)
  all_goals
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    norm_num [first1, second1, demand3, basis, typeDegVec, Finset.sum_singleton]
      at h0 h1 h2 h3 ⊢
    omega

theorem F2_upper_fork_of_coefficients (r : Fin 2) (x y z : ℕ)
    (h : Realizable F2 (upper2 r) (demand3 (central2 r) 0 1 x y z)) :
    Fork x y z := by
  obtain ⟨c, h⟩ := h
  rw [F2_upper_inventory] at h
  refine ⟨c {upper2 r, central2 r, 0}, c {upper2 r, central2 r, 1},
    c {upper2 r, 0, 0}, c {upper2 r, 1, 1}, ?_⟩
  fin_cases r <;> (repeat rw [Finset.sum_insert (by decide)] at h)
  all_goals
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    have h3 := congrFun h 3
    norm_num [upper2, central2, demand3, basis, typeDegVec, Finset.sum_singleton]
      at h0 h1 h2 h3 ⊢
    omega

theorem F1_hole_iff (r : Fin 4) (x y z : ℕ)
    (hc : x ≤ y + z) (hp : (x + y + z) % 2 = 0) :
    ¬ Realizable F1 r (demand3 r (first1 r) (second1 r) x y z) ↔
      x = 0 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
  rw [← fork_hole_iff x y z hc hp]
  constructor
  · intro h hf
    exact h (F1_coefficients r x y z hc hp ((fork_iff x y z).mp hf).2.2)
  · intro h hr
    exact h (F1_fork_of_coefficients r x y z hr)

theorem F2_upper_hole_iff (r : Fin 2) (x y z : ℕ)
    (hc : x ≤ y + z) (hp : (x + y + z) % 2 = 0) :
    ¬ Realizable F2 (upper2 r) (demand3 (central2 r) 0 1 x y z) ↔
      x = 0 ∧ y % 2 = 1 ∧ z % 2 = 1 := by
  rw [← fork_hole_iff x y z hc hp]
  constructor
  · intro h hf
    exact h (F2_upper_coefficients r x y z hc hp ((fork_iff x y z).mp hf).2.2)
  · intro h hr
    exact h (F2_upper_fork_of_coefficients r x y z hr)

theorem F0_coefficients_iff (r : Fin 2) (x y : ℕ) :
    Realizable F0 r (demand2 r (other0 r) x y) ↔ x ≤ y ∧ (x + y) % 2 = 0 := by
  constructor
  · intro h
    exact (wedge_iff x y).mp (F0_wedge_of_coefficients r x y h)
  · rintro ⟨hc, hp⟩
    exact F0_coefficients r x y hc hp

theorem F1_coefficients_iff (r : Fin 4) (x y z : ℕ) :
    Realizable F1 r (demand3 r (first1 r) (second1 r) x y z) ↔
      x ≤ y + z ∧ (x + y + z) % 2 = 0 ∧ (0 < x ∨ y % 2 = 0) := by
  constructor
  · intro h
    exact (fork_iff x y z).mp (F1_fork_of_coefficients r x y z h)
  · rintro ⟨hc, hp, hb⟩
    exact F1_coefficients r x y z hc hp hb

theorem F2_lower_coefficients_iff (r : Fin 2) (x y z : ℕ) :
    Realizable F2 (lower2 r) (demand3 (lower2 r) 2 3 x y z) ↔
      x ≤ y + z ∧ y ≤ x + z ∧ z ≤ x + y ∧ (x + y + z) % 2 = 0 := by
  constructor
  · intro h
    exact (triangle_iff x y z).mp (F2_lower_triangle_of_coefficients r x y z h)
  · rintro ⟨hx, hy, hz, hp⟩
    exact F2_lower_coefficients r x y z hx hy hz hp

theorem F2_upper_coefficients_iff (r : Fin 2) (x y z : ℕ) :
    Realizable F2 (upper2 r) (demand3 (central2 r) 0 1 x y z) ↔
      x ≤ y + z ∧ (x + y + z) % 2 = 0 ∧ (0 < x ∨ y % 2 = 0) := by
  constructor
  · intro h
    exact (fork_iff x y z).mp (F2_upper_fork_of_coefficients r x y z h)
  · rintro ⟨hc, hp, hb⟩
    exact F2_upper_coefficients r x y z hc hp hb

theorem F3_coefficients_iff (r : Fin 4) (x y z : ℕ) :
    Realizable F3 r (demand3 (others3 r 0) (others3 r 1) (others3 r 2) x y z) ↔
      x ≤ y + z ∧ y ≤ x + z ∧ z ≤ x + y ∧ (x + y + z) % 2 = 0 := by
  constructor
  · intro h
    exact (triangle_iff x y z).mp (F3_triangle_of_coefficients r x y z h)
  · rintro ⟨hx, hy, hz, hp⟩
    exact F3_coefficients r x y z hx hy hz hp

end PartitionedTriangleAbsorption.TypedApplicationLinks
