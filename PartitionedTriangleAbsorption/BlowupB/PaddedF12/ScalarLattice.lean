/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Std

@[expose] public section

/-!
# The integer edge-count lattices of F1 and F2

All variables are *unordered* edge counts: an internal edge contributes one to
`d0`, etc. The diagonal entries in the original `edgeVec` convention are twice
these variables. This file proves the exact finite-dimensional integer algebra;
it does not identify a graph predicate with these scalar variables by assumption.
-/

namespace PaddedF12

/-- Coefficients are ordered as 002, 003, 112, 113, 022, 122, 033, 133. -/
def F1Lattice (d0 d1 d2 d3 x02 x03 x12 x13 : Int) : Prop :=
  ∃ a b c d e f g h : Int,
    d0 = a + b ∧ d1 = c + d ∧ d2 = e + f ∧ d3 = g + h ∧
    x02 = 2 * (a + e) ∧ x03 = 2 * (b + g) ∧
    x12 = 2 * (c + f) ∧ x13 = 2 * (d + h)

/-- Coefficients are ordered as 002, 003, 112, 113, 023, 123. -/
def F2Lattice (d0 d1 x02 x03 x12 x13 x23 : Int) : Prop :=
  ∃ a b c d e f : Int,
    d0 = a + b ∧ d1 = c + d ∧
    x02 = 2 * a + e ∧ x03 = 2 * b + e ∧
    x12 = 2 * c + f ∧ x13 = 2 * d + f ∧ x23 = e + f

def freeCharge (base cross : Int) : Int := 4 * base - 2 * cross

theorem f1_lattice_iff (d0 d1 d2 d3 x02 x03 x12 x13 : Int) :
    F1Lattice d0 d1 d2 d3 x02 x03 x12 x13 ↔
      x02 + x03 + x12 + x13 = 2 * (d0 + d1 + d2 + d3) ∧
      2 ∣ x02 ∧ 2 ∣ x03 ∧ 2 ∣ x12 ∧ 2 ∣ x13 := by
  constructor
  · rintro ⟨a, b, c, d, e, f, g, h, h0, h1, h2, h3, h02, h03, h12, h13⟩
    exact ⟨by omega, ⟨a + e, h02⟩, ⟨b + g, h03⟩,
      ⟨c + f, h12⟩, ⟨d + h, h13⟩⟩
  · rintro ⟨hQ, ⟨s02, h02⟩, ⟨s03, h03⟩, ⟨s12, h12⟩, ⟨s13, h13⟩⟩
    refine ⟨d0, 0, s02 + s12 - d2 - d0, d1 - (s02 + s12 - d2 - d0),
      s02 - d0, s12 - (s02 + s12 - d2 - d0), s03,
      s13 - (d1 - (s02 + s12 - d2 - d0)), ?_⟩
    omega

/-- Even degrees in each physical vertex imply these class-cut parities. -/
theorem f1_lattice_iff_one_bit (d0 d1 d2 d3 x02 x03 x12 x13 : Int)
    (hr0 : 2 ∣ x02 + x03) (hr1 : 2 ∣ x12 + x13)
    (hr2 : 2 ∣ x02 + x12) :
    F1Lattice d0 d1 d2 d3 x02 x03 x12 x13 ↔
      x02 + x03 + x12 + x13 = 2 * (d0 + d1 + d2 + d3) ∧ 2 ∣ x02 := by
  rw [f1_lattice_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hQ, ⟨s02, h02⟩⟩
    obtain ⟨r0, h0⟩ := hr0
    obtain ⟨r1, h1⟩ := hr1
    obtain ⟨r2, h2⟩ := hr2
    exact ⟨hQ, ⟨s02, h02⟩, ⟨r0 - s02, by omega⟩,
      ⟨r2 - s02, by omega⟩, ⟨r1 - r2 + s02, by omega⟩⟩

theorem f2_lattice_iff (d0 d1 x02 x03 x12 x13 x23 : Int) :
    F2Lattice d0 d1 x02 x03 x12 x13 x23 ↔
      x02 + x03 + x12 + x13 = 2 * (d0 + d1 + x23) ∧
      4 ∣ x02 - x03 + 2 * d0 ∧ 4 ∣ x12 - x13 + 2 * d1 := by
  constructor
  · rintro ⟨a, b, c, d, e, f, h0, h1, h02, h03, h12, h13, h23⟩
    exact ⟨by omega, ⟨a, by omega⟩, ⟨c, by omega⟩⟩
  · rintro ⟨hQ, ⟨a, ha⟩, ⟨c, hc⟩⟩
    refine ⟨a, d0 - a, c, d1 - c, x02 - 2 * a, x12 - 2 * c, ?_⟩
    omega

/-- With the class-2 degree parity, the second mod-4 condition follows from the first. -/
theorem f2_lattice_iff_one_bit (d0 d1 x02 x03 x12 x13 x23 : Int)
    (hr2 : 2 ∣ x02 + x12 + x23) :
    F2Lattice d0 d1 x02 x03 x12 x13 x23 ↔
      x02 + x03 + x12 + x13 = 2 * (d0 + d1 + x23) ∧
      4 ∣ x02 - x03 + 2 * d0 := by
  rw [f2_lattice_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hQ, ⟨a, ha⟩⟩
    obtain ⟨r2, h2⟩ := hr2
    exact ⟨hQ, ⟨a, ha⟩, ⟨r2 - x23 - a, by omega⟩⟩

theorem f2_torsion_numerator_even (d0 x02 x03 : Int)
    (hr0 : 2 ∣ x02 + x03) : 2 ∣ x02 - x03 + 2 * d0 := by
  obtain ⟨r0, h0⟩ := hr0
  exact ⟨r0 - x03 + d0, by omega⟩

/-- The normalized mod-4 obstruction really is one bit on an even graph. -/
theorem f2_torsion_iff (d0 x02 x03 : Int) (hr0 : 2 ∣ x02 + x03) :
    4 ∣ x02 - x03 + 2 * d0 ↔ 2 ∣ (x02 - x03 + 2 * d0) / 2 := by
  have h := f2_torsion_numerator_even d0 x02 x03 hr0
  obtain ⟨k, hk⟩ := h
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by omega⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by omega⟩

/-- The charge unit is 12 on an ordinary triangle-divisible edge set.
`base + cross` is its total edge count, and `cross` is a cut size. -/
theorem twelve_dvd_freeCharge (base cross : Int)
    (hthree : 3 ∣ base + cross) (htwo : 2 ∣ cross) :
    12 ∣ freeCharge base cross := by
  obtain ⟨s, hs⟩ := hthree
  obtain ⟨k, hk⟩ := htwo
  refine ⟨(base - s) / 2, ?_⟩
  unfold freeCharge
  omega

theorem freeCharge_zero_iff (base cross : Int) :
    freeCharge base cross = 0 ↔ cross = 2 * base := by
  unfold freeCharge
  omega

theorem freeCharge_zero_three_dvd (base cross : Int)
    (h : freeCharge base cross = 0) : 3 ∣ base + cross := by
  have := (freeCharge_zero_iff base cross).mp h
  exact ⟨base, by omega⟩

/-- C3 inside class 0 has positive unit charge; C6 alternating classes 0 and 2 has negative unit. -/
theorem charge_token_values :
    freeCharge 3 0 = 12 ∧ freeCharge 0 6 = -12 := by decide

/-- C6 with class sequence 0,0,0,2,1,3: zero charge but nontrivial F1 torsion. -/
theorem f1_torsion_token_values :
    freeCharge 2 4 = 0 ∧ ¬ (2 : Int) ∣ 1 ∧
      ¬ F1Lattice 2 0 0 0 1 1 1 1 := by
  refine ⟨by decide, by omega, ?_⟩
  rw [f1_lattice_iff]
  omega

/-- C6 with class sequence 0,0,0,2,1,2: zero charge but nontrivial F2 torsion. -/
theorem f2_torsion_token_values :
    freeCharge 2 4 = 0 ∧ (2 - 0 + 2 * (2 : Int)) / 2 % 2 = 1 ∧
      ¬ F2Lattice 2 0 2 0 2 0 0 := by
  refine ⟨by decide, by decide, ?_⟩
  rw [f2_lattice_iff]
  omega

#print axioms f1_lattice_iff
#print axioms f1_lattice_iff_one_bit
#print axioms f2_lattice_iff
#print axioms f2_lattice_iff_one_bit
#print axioms f2_torsion_iff
#print axioms twelve_dvd_freeCharge
#print axioms f1_torsion_token_values
#print axioms f2_torsion_token_values

end PaddedF12
