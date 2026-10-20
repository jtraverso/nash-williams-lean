/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLinkCoefficients
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-! # The F0--F3 vertex-link dictionaries

Every inventory below lists all types containing the root. The conclusions
give natural coefficients in `typeDegVec`, not simultaneous graph embeddings.
In the fork cases the extra boundary-parity hypothesis cannot be dropped;
adding one permitted pair repairs it at the coefficient level.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedApplicationLinks

open Finset TypedLinkArithmetic TypedLinkCoefficients

def F0 : Finset (Multiset (Fin 2)) := {{0, 0, 1}, {0, 1, 1}}

def F1 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 2}, {0, 0, 3}, {1, 1, 2}, {1, 1, 3},
    {0, 2, 2}, {1, 2, 2}, {0, 3, 3}, {1, 3, 3}}

def F2 : Finset (Multiset (Fin 4)) :=
  {{0, 0, 2}, {0, 0, 3}, {1, 1, 2}, {1, 1, 3}, {0, 2, 3}, {1, 2, 3}}

def F3 : Finset (Multiset (Fin 4)) :=
  {{0, 1, 2}, {0, 1, 3}, {0, 2, 3}, {1, 2, 3}}

def other0 : Fin 2 → Fin 2 := ![1, 0]
def first1 : Fin 4 → Fin 4 := ![2, 2, 0, 0]
def second1 : Fin 4 → Fin 4 := ![3, 3, 1, 1]
def lower2 : Fin 2 → Fin 4 := ![0, 1]
def upper2 : Fin 2 → Fin 4 := ![2, 3]
def central2 : Fin 2 → Fin 4 := ![3, 2]
def others3 : Fin 4 → Fin 3 → Fin 4 :=
  ![![1, 2, 3], ![0, 2, 3], ![0, 1, 3], ![0, 1, 2]]

theorem F0_inventory (r : Fin 2) :
    F0.filter (r ∈ ·) = {{r, r, other0 r}, {r, other0 r, other0 r}} := by
  revert r
  decide

theorem F1_inventory (r : Fin 4) :
    F1.filter (r ∈ ·) =
      {{r, r, first1 r}, {r, r, second1 r},
        {r, first1 r, first1 r}, {r, second1 r, second1 r}} := by
  revert r
  decide

theorem F2_lower_inventory (r : Fin 2) :
    F2.filter (lower2 r ∈ ·) =
      {{lower2 r, lower2 r, 2}, {lower2 r, lower2 r, 3}, {lower2 r, 2, 3}} := by
  revert r
  decide

theorem F2_upper_inventory (r : Fin 2) :
    F2.filter (upper2 r ∈ ·) =
      {{upper2 r, central2 r, 0}, {upper2 r, central2 r, 1},
        {upper2 r, 0, 0}, {upper2 r, 1, 1}} := by
  revert r
  decide

theorem F3_inventory (r : Fin 4) :
    F3.filter (r ∈ ·) =
      {{r, others3 r 0, others3 r 1}, {r, others3 r 0, others3 r 2},
        {r, others3 r 1, others3 r 2}} := by
  revert r
  decide

theorem F0_coefficients (r : Fin 2) (x y : ℕ)
    (hcone : x ≤ y) (hparity : (x + y) % 2 = 0) :
    Realizable F0 r (demand2 r (other0 r) x y) := by
  apply wedge F0 r (other0 r) x y
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · exact (wedge_iff x y).mpr ⟨hcone, hparity⟩

theorem F1_coefficients (r : Fin 4) (x y z : ℕ)
    (hcone : x ≤ y + z) (hparity : (x + y + z) % 2 = 0)
    (hboundary : 0 < x ∨ y % 2 = 0) :
    Realizable F1 r (demand3 r (first1 r) (second1 r) x y z) := by
  apply fork F1 r r (first1 r) (second1 r) x y z
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · exact (fork_iff x y z).mpr ⟨hcone, hparity, hboundary⟩

theorem F1_corrected_coefficients (r : Fin 4) (x y z : ℕ)
    (hcone : x ≤ y + z) (hparity : (x + y + z) % 2 = 0) :
    Realizable F1 r (demand3 r (first1 r) (second1 r) (x + 1) (y + 1) z) := by
  apply F1_coefficients
  · omega
  · omega
  · exact Or.inl (by omega)

theorem F2_lower_coefficients (r : Fin 2) (x y z : ℕ)
    (hx : x ≤ y + z) (hy : y ≤ x + z) (hz : z ≤ x + y)
    (hparity : (x + y + z) % 2 = 0) :
    Realizable F2 (lower2 r) (demand3 (lower2 r) 2 3 x y z) := by
  apply triangle F2 (lower2 r) (lower2 r) 2 3 x y z
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · exact (triangle_iff x y z).mpr ⟨hx, hy, hz, hparity⟩

theorem F2_upper_coefficients (r : Fin 2) (x y z : ℕ)
    (hcone : x ≤ y + z) (hparity : (x + y + z) % 2 = 0)
    (hboundary : 0 < x ∨ y % 2 = 0) :
    Realizable F2 (upper2 r) (demand3 (central2 r) 0 1 x y z) := by
  apply fork F2 (upper2 r) (central2 r) 0 1 x y z
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · exact (fork_iff x y z).mpr ⟨hcone, hparity, hboundary⟩

theorem F2_upper_corrected_coefficients (r : Fin 2) (x y z : ℕ)
    (hcone : x ≤ y + z) (hparity : (x + y + z) % 2 = 0) :
    Realizable F2 (upper2 r) (demand3 (central2 r) 0 1 (x + 1) (y + 1) z) := by
  apply F2_upper_coefficients
  · omega
  · omega
  · exact Or.inl (by omega)

theorem F3_coefficients (r : Fin 4) (x y z : ℕ)
    (hx : x ≤ y + z) (hy : y ≤ x + z) (hz : z ≤ x + y)
    (hparity : (x + y + z) % 2 = 0) :
    Realizable F3 r (demand3 (others3 r 0) (others3 r 1) (others3 r 2) x y z) := by
  apply triangle F3 r (others3 r 0) (others3 r 1) (others3 r 2) x y z
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · fin_cases r <;> decide
  · exact (triangle_iff x y z).mpr ⟨hx, hy, hz, hparity⟩

end PartitionedTriangleAbsorption.TypedApplicationLinks
