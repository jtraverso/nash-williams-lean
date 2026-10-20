/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.ScalarLattice

/-!
# Explicit coefficient budgets for F1 and F2

For unordered physical edge counts between zero and `K`, the explicit integer
witnesses have every coefficient of absolute value at most `4 K`, and total
negative mass at most `32 K`. Thus no finite-choice bound is required to choose
the size of a terminal coloured-hub absorber.
-/

namespace PaddedF12

theorem natAbs_le_of_bounds {z : Int} {b : Nat}
    (hlo : -(b : Int) ≤ z) (hhi : z ≤ (b : Int)) : z.natAbs ≤ b := by
  cases z with
  | ofNat n =>
    change (n : Int) ≤ (b : Int) at hhi
    change n ≤ b
    omega
  | negSucc n => change n + 1 ≤ b; omega

theorem negative_part_le_natAbs (z : Int) : (-z).toNat ≤ z.natAbs := by
  cases z <;> omega

/-- The explicit F1 witness, with uniform coefficient and negative-mass bounds. -/
theorem f1_bounded_witness (K : Nat) (d0 d1 d2 d3 x02 x03 x12 x13 : Int)
    (hcounts : ∀ z ∈ [d0, d1, d2, d3, x02, x03, x12, x13], 0 ≤ z ∧ z ≤ (K : Int))
    (hlat : F1Lattice d0 d1 d2 d3 x02 x03 x12 x13) :
    ∃ a b c d e f g h : Int,
      (d0 = a + b ∧ d1 = c + d ∧ d2 = e + f ∧ d3 = g + h ∧
        x02 = 2 * (a + e) ∧ x03 = 2 * (b + g) ∧
        x12 = 2 * (c + f) ∧ x13 = 2 * (d + h)) ∧
      (∀ z ∈ [a, b, c, d, e, f, g, h], z.natAbs ≤ 4 * K) ∧
      (-a).toNat + (-b).toNat + (-c).toNat + (-d).toNat +
        (-e).toNat + (-f).toNat + (-g).toNat + (-h).toNat ≤ 32 * K := by
  have hd0 := hcounts d0 (by simp)
  have hd1 := hcounts d1 (by simp)
  have hd2 := hcounts d2 (by simp)
  have hd3 := hcounts d3 (by simp)
  have hx02 := hcounts x02 (by simp)
  have hx03 := hcounts x03 (by simp)
  have hx12 := hcounts x12 (by simp)
  have hx13 := hcounts x13 (by simp)
  obtain ⟨hQ, ⟨s02, h02⟩, ⟨s03, h03⟩, ⟨s12, h12⟩, ⟨s13, h13⟩⟩ :=
    (f1_lattice_iff d0 d1 d2 d3 x02 x03 x12 x13).mp hlat
  let z : Int := s02 + s12 - d2 - d0
  have hbounded : ∀ v ∈ [d0, 0, z, d1 - z, s02 - d0, s12 - z, s03, s13 - d1 + z],
      v.natAbs ≤ 4 * K := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply natAbs_le_of_bounds <;> dsimp [z] <;> omega
  have hn0 := Nat.le_trans (negative_part_le_natAbs d0) (hbounded d0 (by simp))
  have hn1 := Nat.le_trans (negative_part_le_natAbs 0) (hbounded 0 (by simp))
  have hn2 := Nat.le_trans (negative_part_le_natAbs z) (hbounded z (by simp))
  have hn3 := Nat.le_trans (negative_part_le_natAbs (d1 - z)) (hbounded (d1 - z) (by simp))
  have hn4 := Nat.le_trans (negative_part_le_natAbs (s02 - d0)) (hbounded (s02 - d0) (by simp))
  have hn5 := Nat.le_trans (negative_part_le_natAbs (s12 - z)) (hbounded (s12 - z) (by simp))
  have hn6 := Nat.le_trans (negative_part_le_natAbs s03) (hbounded s03 (by simp))
  have hn7 := Nat.le_trans (negative_part_le_natAbs (s13 - d1 + z)) (hbounded (s13 - d1 + z) (by simp))
  refine ⟨d0, 0, z, d1 - z, s02 - d0, s12 - z, s03, s13 - d1 + z, ?_, hbounded, ?_⟩
  · dsimp [z]
    omega
  · omega

/-- The six F2 coefficients satisfy the same uniform `32 K` negative budget. -/
theorem f2_bounded_witness (K : Nat) (d0 d1 x02 x03 x12 x13 x23 : Int)
    (hcounts : ∀ z ∈ [d0, d1, x02, x03, x12, x13, x23], 0 ≤ z ∧ z ≤ (K : Int))
    (hlat : F2Lattice d0 d1 x02 x03 x12 x13 x23) :
    ∃ a b c d e f : Int,
      (d0 = a + b ∧ d1 = c + d ∧ x02 = 2 * a + e ∧ x03 = 2 * b + e ∧
        x12 = 2 * c + f ∧ x13 = 2 * d + f ∧ x23 = e + f) ∧
      (∀ z ∈ [a, b, c, d, e, f], z.natAbs ≤ 4 * K) ∧
      (-a).toNat + (-b).toNat + (-c).toNat + (-d).toNat +
        (-e).toNat + (-f).toNat ≤ 32 * K := by
  have hd0 := hcounts d0 (by simp)
  have hd1 := hcounts d1 (by simp)
  have hx02 := hcounts x02 (by simp)
  have hx03 := hcounts x03 (by simp)
  have hx12 := hcounts x12 (by simp)
  have hx13 := hcounts x13 (by simp)
  have hx23 := hcounts x23 (by simp)
  obtain ⟨hQ, ⟨a, ha⟩, ⟨c, hc⟩⟩ := (f2_lattice_iff d0 d1 x02 x03 x12 x13 x23).mp hlat
  have hbounded : ∀ v ∈ [a, d0 - a, c, d1 - c, x02 - 2 * a, x12 - 2 * c],
      v.natAbs ≤ 4 * K := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply natAbs_le_of_bounds <;> omega
  have hn0 := Nat.le_trans (negative_part_le_natAbs a) (hbounded a (by simp))
  have hn1 := Nat.le_trans (negative_part_le_natAbs (d0 - a)) (hbounded (d0 - a) (by simp))
  have hn2 := Nat.le_trans (negative_part_le_natAbs c) (hbounded c (by simp))
  have hn3 := Nat.le_trans (negative_part_le_natAbs (d1 - c)) (hbounded (d1 - c) (by simp))
  have hn4 := Nat.le_trans (negative_part_le_natAbs (x02 - 2 * a)) (hbounded (x02 - 2 * a) (by simp))
  have hn5 := Nat.le_trans (negative_part_le_natAbs (x12 - 2 * c)) (hbounded (x12 - 2 * c) (by simp))
  refine ⟨a, d0 - a, c, d1 - c, x02 - 2 * a, x12 - 2 * c, ?_, hbounded, ?_⟩ <;> omega

/-- The explicit hub budgets used for the 144-edge final library. -/
theorem terminal_hub_numeric_budget :
    105 * 144 + 318 * (32 * 144) = 1480464 ∧
    34 * 144 + 105 * (32 * 144) + 4 = 488740 ∧
    1480464 ≤ 2 ^ 21 ∧ 488740 ≤ 2 ^ 21 ∧ 2 ^ 21 + 288 < 2 ^ 22 := by decide

#print axioms f1_bounded_witness
#print axioms f2_bounded_witness
#print axioms terminal_hub_numeric_budget

end PaddedF12
