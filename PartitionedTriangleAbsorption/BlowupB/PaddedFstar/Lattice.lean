/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PhysicalCharge
import PartitionedTriangleAbsorption.TypedBoundedCoefficients

/-!
# The family F* and its trivial lattice

`Fstar = {000, 001, 002, 012, 123, 133, 233, 333}` on four classes. Its allowed pairs are
00, 01, 02, 12, 13, 23 and 33; the pairs 03, 11 and 22 are forbidden. The local census
(`cegis/b0_refiner/Fstar_20261012/`) found it as the unique family, up to S₄, whose integral
lattice is trivial (`IsIntDiv` = ordinary divisibility on allowed support) and which also has
`ThreeStepLinks` and common neighbour classes. The edge-lattice identity `L_F* = Λ_ord` is
certified by certo (Smith 1,1,1,1,2,2,6 on both sides) and jacobian (equal Hermite forms).

Lean content:
* `isIntDiv_Fstar_iff`: on loopless sets, `IsIntDiv p Fstar E ↔ ActiveEdges ∧ Even3 E`;
* `fstar_bounded_coefficients`: an integral witness with negative mass `≤ 2 |E| + 14`. The
  explicit witness (parameter `s ∈ [0, 6)` chosen by CRT) was first checked by certo/z3.
-/

namespace PaddedFstar

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedBoundedCoefficients
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PaddedF12

/-- The family F*. -/
def Fstar : Finset (Multiset (Fin 4)) :=
  {{0, 0, 0}, {0, 0, 1}, {0, 0, 2}, {0, 1, 2}, {1, 2, 3}, {1, 3, 3}, {2, 3, 3}, {3, 3, 3}}

theorem Fstar_card : ∀ τ ∈ Fstar, Multiset.card τ = 3 := by decide

theorem Fstar_three_step : ThreeStepLinks Fstar := by
  unfold ThreeStepLinks Link Fstar
  decide

/-- The explicit coefficients, indexed by type. -/
def fstarCoeff (a000 a001 a002 a012 a123 a133 a233 a333 : ℤ) (τ : Multiset (Fin 4)) : ℤ :=
  if τ = {0, 0, 0} then a000 else if τ = {0, 0, 1} then a001 else
  if τ = {0, 0, 2} then a002 else if τ = {0, 1, 2} then a012 else
  if τ = {1, 2, 3} then a123 else if τ = {1, 3, 3} then a133 else
  if τ = {2, 3, 3} then a233 else if τ = {3, 3, 3} then a333 else 0

/-- The ordered edge matrix of F*-supported counts. -/
def fstarMatrix (d0 x01 x02 x12 x13 x23 d3 : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![2 * d0, x01, x02, 0], ![x01, 0, x12, x13],
    ![x02, x12, 0, x23], ![0, x13, x23, 2 * d3]]

theorem sum_Fstar {β : Type*} [AddCommMonoid β] (f : Multiset (Fin 4) → β) :
    ∑ τ ∈ Fstar, f τ = f {0, 0, 0} + f {0, 0, 1} + f {0, 0, 2} + f {0, 1, 2} +
      f {1, 2, 3} + f {1, 3, 3} + f {2, 3, 3} + f {3, 3, 3} := by
  unfold Fstar
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  abel

theorem fstar_edge_lattice_matrix (c : Multiset (Fin 4) → ℤ) :
    (∑ τ ∈ Fstar, c τ • typeEdgeVec τ) =
      fstarMatrix (3 * c {0, 0, 0} + c {0, 0, 1} + c {0, 0, 2}) (2 * c {0, 0, 1} + c {0, 1, 2})
        (2 * c {0, 0, 2} + c {0, 1, 2}) (c {0, 1, 2} + c {1, 2, 3})
        (c {1, 2, 3} + 2 * c {1, 3, 3}) (c {1, 2, 3} + 2 * c {2, 3, 3})
        (c {1, 3, 3} + c {2, 3, 3} + 3 * c {3, 3, 3}) := by
  rw [sum_Fstar]
  funext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fstarMatrix, typeEdgeVec] <;> ring

variable {V : Type*} [DecidableEq V]

theorem fstar_inactive_counts (p : V → Fin 4) (E : Finset (Sym2 V))
    (h : ActiveEdges Fstar p E) :
    unorderedCount p E 0 3 = 0 ∧ unorderedCount p E 1 1 = 0 ∧ unorderedCount p E 2 2 = 0 := by
  have hf : ∀ a b k : Fin 4, Link Fstar a b k →
      s(a, b) ≠ s(0, 3) ∧ s(a, b) ≠ s(1, 1) ∧ s(a, b) ≠ s(2, 2) := by
    unfold Link Fstar; decide
  refine ⟨?_, ?_, ?_⟩ <;> apply unorderedCount_zero_of_forbidden <;> intro e he <;>
    induction e using Sym2.ind with
    | _ a b =>
      obtain ⟨k, hk⟩ := h a b he
      have := hf (p a) (p b) k hk
      first | exact this.1 | exact this.2.1 | exact this.2.2

theorem edgeVec_fstarMatrix (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges Fstar p E) :
    edgeVec p E = fstarMatrix (unorderedCount p E 0 0) (unorderedCount p E 0 1)
      (unorderedCount p E 0 2) (unorderedCount p E 1 2) (unorderedCount p E 1 3)
      (unorderedCount p E 2 3) (unorderedCount p E 3 3) := by
  obtain ⟨h03, h11, h22⟩ := fstar_inactive_counts p E h
  funext i j
  rw [edgeVec_unorderedCount]
  fin_cases i <;> fin_cases j <;>
    simp [fstarMatrix, unorderedCount_swap p E 1 0, unorderedCount_swap p E 2 0,
      unorderedCount_swap p E 2 1, unorderedCount_swap p E 3 0,
      unorderedCount_swap p E 3 1, unorderedCount_swap p E 3 2, h03, h11, h22]

theorem fstar_total_count (p : V → Fin 4) (E : Finset (Sym2 V)) (h : ActiveEdges Fstar p E) :
    (E.card : ℤ) = unorderedCount p E 0 0 + unorderedCount p E 0 1 + unorderedCount p E 0 2 +
      unorderedCount p E 1 2 + unorderedCount p E 1 3 + unorderedCount p E 2 3 +
      unorderedCount p E 3 3 := by
  have htotal := total_edgeVec p E
  rw [edgeVec_fstarMatrix p E h] at htotal
  norm_num [fstarMatrix, Fin.sum_univ_succ] at htotal
  omega

theorem fstar_class_parities [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hact : ActiveEdges Fstar p E) (hloop : ∀ e ∈ E, ¬ e.IsDiag)
    (heven : ∀ v, Even (incidentLoad E v)) :
    (2 : ℤ) ∣ unorderedCount p E 0 1 + unorderedCount p E 0 2 ∧
    (2 : ℤ) ∣ unorderedCount p E 0 1 + unorderedCount p E 1 2 + unorderedCount p E 1 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 0 2 + unorderedCount p E 1 2 + unorderedCount p E 2 3 ∧
    (2 : ℤ) ∣ unorderedCount p E 1 3 + unorderedCount p E 2 3 := by
  obtain ⟨k0, hk0⟩ := class_row_two_dvd p E hloop heven 0
  obtain ⟨k1, hk1⟩ := class_row_two_dvd p E hloop heven 1
  obtain ⟨k2, hk2⟩ := class_row_two_dvd p E hloop heven 2
  obtain ⟨k3, hk3⟩ := class_row_two_dvd p E hloop heven 3
  rw [edgeVec_fstarMatrix p E hact] at hk0 hk1 hk2 hk3
  norm_num [fstarMatrix, Fin.sum_univ_succ] at hk0 hk1 hk2 hk3
  exact ⟨⟨k0 - unorderedCount p E 0 0, by omega⟩, ⟨k1, by omega⟩, ⟨k2, by omega⟩,
    ⟨k3 - unorderedCount p E 3 3, by omega⟩⟩

/-- The explicit witness for scalar counts (checked first by certo/z3). -/
theorem fstar_scalar_witness (d0 x01 x02 x12 x13 x23 d3 : ℤ)
    (hn : 0 ≤ d0 ∧ 0 ≤ x01 ∧ 0 ≤ x02 ∧ 0 ≤ x12 ∧ 0 ≤ x13 ∧ 0 ≤ x23 ∧ 0 ≤ d3)
    (hp0 : (2 : ℤ) ∣ x01 + x02) (hp1 : (2 : ℤ) ∣ x01 + x12 + x13)
    (hp2 : (2 : ℤ) ∣ x02 + x12 + x23) (hp3 : (2 : ℤ) ∣ x13 + x23)
    (h3 : (3 : ℤ) ∣ d0 + x01 + x02 + x12 + x13 + x23 + d3) :
    ∃ a000 a001 a002 a012 a123 a133 a233 a333 : ℤ,
      d0 = 3 * a000 + a001 + a002 ∧ x01 = 2 * a001 + a012 ∧ x02 = 2 * a002 + a012 ∧
      x12 = a012 + a123 ∧ x13 = a123 + 2 * a133 ∧ x23 = a123 + 2 * a233 ∧
      d3 = a133 + a233 + 3 * a333 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a000 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a001 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a002 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a012 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a123 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a133 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a233 ∧
      -(d0 + x01 + x02 + x12 + x13 + x23 + d3 + 5) ≤ a333 := by
  obtain ⟨hd0, h01, h02, h12, h13, h23, hd3⟩ := hn
  obtain ⟨k0, hk0⟩ := hp0
  obtain ⟨k3, hk3⟩ := hp3
  obtain ⟨s, hs0, hs5, hs2, hs3⟩ : ∃ s : ℤ, 0 ≤ s ∧ s ≤ 5 ∧ (s - x01) % 2 = 0 ∧
      (s - (k0 - d0)) % 3 = 0 :=
    ⟨(3 * (x01 % 2) + 4 * ((k0 - d0) % 3)) % 6, by omega, by omega, by omega, by omega⟩
  have e1 : (x01 - s) % 2 = 0 := by omega
  have e2 : (x02 - s) % 2 = 0 := by omega
  have e5 : (x13 - x12 + s) % 2 = 0 := by obtain ⟨k1, hk1⟩ := hp1; omega
  have e6 : (x23 - x12 + s) % 2 = 0 := by obtain ⟨k2, hk2⟩ := hp2; omega
  have e0 : (d0 - k0 + s) % 3 = 0 := by omega
  have e7 : (d3 - k3 + x12 - s) % 3 = 0 := by obtain ⟨k, hk⟩ := h3; omega
  refine ⟨(d0 - k0 + s) / 3, (x01 - s) / 2, (x02 - s) / 2, s, x12 - s, (x13 - x12 + s) / 2,
    (x23 - x12 + s) / 2, (d3 - k3 + x12 - s) / 3, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals clear e0 e1 e2 e5 e6 e7 hs2 hs3 hp1 hp2 h3
  all_goals omega

theorem fc0 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {0, 0, 0} = a := by
  unfold fstarCoeff; rw [if_pos rfl]
theorem fc1 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {0, 0, 1} = b := by
  unfold fstarCoeff; rw [if_neg (by decide), if_pos rfl]
theorem fc2 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {0, 0, 2} = c := by
  unfold fstarCoeff; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem fc3 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {0, 1, 2} = d := by
  unfold fstarCoeff; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem fc4 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {1, 2, 3} = e := by
  unfold fstarCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem fc5 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {1, 3, 3} = f := by
  unfold fstarCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_pos rfl]
theorem fc6 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {2, 3, 3} = g := by
  unfold fstarCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_pos rfl]
theorem fc7 (a b c d e f g h : ℤ) : fstarCoeff a b c d e f g h {3, 3, 3} = h := by
  unfold fstarCoeff
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

/-- **Trivial lattice**: F*-divisibility is ordinary divisibility on allowed support. -/
theorem isIntDiv_Fstar_iff [Fintype V] (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p Fstar E ↔ ActiveEdges Fstar p E ∧ OnePart.Even3 E := by
  rw [TypedDivisibilityCollapse.isIntDiv_iff Fstar_three_step Fstar_card hloop]
  constructor
  · rintro ⟨hact, heven, c, hc⟩
    refine ⟨hact, ?_, heven⟩
    have htot := fstar_total_count p E hact
    rw [edgeVec_fstarMatrix p E hact, fstar_edge_lattice_matrix] at hc
    set A0 := c {0, 0, 0} with hA0
    set A1 := c {0, 0, 1} with hA1
    set A2 := c {0, 0, 2} with hA2
    set A3 := c {0, 1, 2} with hA3
    set A4 := c {1, 2, 3} with hA4
    set A5 := c {1, 3, 3} with hA5
    set A6 := c {2, 3, 3} with hA6
    set A7 := c {3, 3, 3} with hA7
    have e00 := congrFun (congrFun hc 0) 0
    have e01 := congrFun (congrFun hc 0) 1
    have e02 := congrFun (congrFun hc 0) 2
    have e12 := congrFun (congrFun hc 1) 2
    have e13 := congrFun (congrFun hc 1) 3
    have e23 := congrFun (congrFun hc 2) 3
    have e33 := congrFun (congrFun hc 3) 3
    simp only [fstarMatrix] at e00 e01 e02 e12 e13 e23 e33
    norm_num at e00 e01 e02 e12 e13 e23 e33
    have h3 : (3 : ℤ) ∣ (E.card : ℤ) := ⟨A0 + A1 + A2 + A3 + A4 + A5 + A6 + A7, by omega⟩
    exact_mod_cast h3
  · rintro ⟨hact, h3, heven⟩
    refine ⟨hact, heven, ?_⟩
    obtain ⟨hp0, hp1, hp2, hp3⟩ := fstar_class_parities p E hact hloop heven
    have htot := fstar_total_count p E hact
    have h3' : (3 : ℤ) ∣ unorderedCount p E 0 0 + unorderedCount p E 0 1 +
        unorderedCount p E 0 2 + unorderedCount p E 1 2 + unorderedCount p E 1 3 +
        unorderedCount p E 2 3 + unorderedCount p E 3 3 := by
      rw [← htot]; exact_mod_cast h3
    obtain ⟨a000, a001, a002, a012, a123, a133, a233, a333, q0, q1, q2, q3, q4, q5, q6,
      -, -, -, -, -, -, -, -⟩ :=
      fstar_scalar_witness _ _ _ _ _ _ _ ⟨unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _⟩ hp0 hp1 hp2 hp3 h3'
    refine ⟨fstarCoeff a000 a001 a002 a012 a123 a133 a233 a333, ?_⟩
    rw [edgeVec_fstarMatrix p E hact, fstar_edge_lattice_matrix]
    rw [fc0, fc1, fc2, fc3, fc4, fc5, fc6, fc7, q0, q1, q2, q3, q4, q5, q6]

/-- **Bounded integral witnesses** for pieces with at most `K` edges (no finiteness needed). -/
theorem fstar_bounded_coefficients (K : ℕ) {W : Type*} [DecidableEq W]
    (p : W → Fin 4) (P : Finset (Sym2 W)) (hK : P.card ≤ K) (hdiv : IsIntDiv p Fstar P) :
    ∃ c : Multiset (Fin 4) → ℤ, edgeVec p P = ∑ τ ∈ Fstar, c τ • typeEdgeVec τ ∧
      negativeMass Fstar c ≤ 8 * K + 40 := by
  have hact := active_of_isIntDiv Fstar_card hdiv
  obtain ⟨c, hc⟩ := hdiv.1
  have htot := fstar_total_count p P hact
  rw [edgeVec_fstarMatrix p P hact, fstar_edge_lattice_matrix] at hc
  set A0 := c {0, 0, 0} with hA0
  set A1 := c {0, 0, 1} with hA1
  set A2 := c {0, 0, 2} with hA2
  set A3 := c {0, 1, 2} with hA3
  set A4 := c {1, 2, 3} with hA4
  set A5 := c {1, 3, 3} with hA5
  set A6 := c {2, 3, 3} with hA6
  set A7 := c {3, 3, 3} with hA7
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e02 := congrFun (congrFun hc 0) 2
  have e12 := congrFun (congrFun hc 1) 2
  have e13 := congrFun (congrFun hc 1) 3
  have e23 := congrFun (congrFun hc 2) 3
  have e33 := congrFun (congrFun hc 3) 3
  simp only [fstarMatrix] at e00 e01 e02 e12 e13 e23 e33
  norm_num at e00 e01 e02 e12 e13 e23 e33
  obtain ⟨a000, a001, a002, a012, a123, a133, a233, a333, q0, q1, q2, q3, q4, q5, q6,
    b0, b1, b2, b3, b4, b5, b6, b7⟩ :=
    fstar_scalar_witness (unorderedCount p P 0 0) (unorderedCount p P 0 1)
      (unorderedCount p P 0 2) (unorderedCount p P 1 2) (unorderedCount p P 1 3)
      (unorderedCount p P 2 3) (unorderedCount p P 3 3)
      ⟨unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _, unorderedCount_nonneg _ _ _ _,
        unorderedCount_nonneg _ _ _ _⟩
      ⟨A1 + A2 + A3, by omega⟩ ⟨A1 + A3 + A4 + A5, by omega⟩ ⟨A2 + A3 + A4 + A6, by omega⟩
      ⟨A4 + A5 + A6, by omega⟩ ⟨A0 + A1 + A2 + A3 + A4 + A5 + A6 + A7, by omega⟩
  refine ⟨fstarCoeff a000 a001 a002 a012 a123 a133 a233 a333, ?_, ?_⟩
  · rw [edgeVec_fstarMatrix p P hact, fstar_edge_lattice_matrix]
    rw [fc0, fc1, fc2, fc3, fc4, fc5, fc6, fc7, q0, q1, q2, q3, q4, q5, q6]
  · unfold negativeMass
    rw [sum_Fstar, fc0, fc1, fc2, fc3, fc4, fc5, fc6, fc7]
    have hKZ : (P.card : ℤ) ≤ K := by exact_mod_cast hK
    rw [← htot] at b0 b1 b2 b3 b4 b5 b6 b7
    clear * - b0 b1 b2 b3 b4 b5 b6 b7 hKZ
    omega

#print axioms isIntDiv_Fstar_iff
#print axioms fstar_bounded_coefficients

end PaddedFstar
