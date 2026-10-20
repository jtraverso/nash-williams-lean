/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedApplicationCorrection

/-! # Original divisibility implies the coordinate hypotheses for F1 and F2

Integral link coefficients give the parity and zero coordinates. Nonnegative
real coefficients give the cone inequalities. No normality of the semigroup
is assumed: its boundary holes are repaired by the physical construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedDivisibilityCoordinates

open Finset TypedApplicationLinks TypedLinkCoefficients TypedApplicationCorrection

def LinkLattice (F : Finset (Multiset (Fin 4))) (r : Fin 4) (d : Fin 4 → ℤ) : Prop :=
  ∃ c : Multiset (Fin 4) → ℤ, d = ∑ τ ∈ F with r ∈ τ, c τ • typeDegVec τ r

def LinkCone (F : Finset (Multiset (Fin 4))) (r : Fin 4) (d : Fin 4 → ℤ) : Prop :=
  ∃ c : Multiset (Fin 4) → ℝ, (∀ τ, 0 ≤ c τ) ∧
    (fun j => (d j : ℝ)) = ∑ τ ∈ F with r ∈ τ, c τ • fun j => (typeDegVec τ r j : ℝ)

theorem F1_coordinates (r : Fin 4) (d : Fin 4 → ℤ) (hn : ∀ j, 0 ≤ d j)
    (hi : LinkLattice F1 r d) (hf : LinkCone F1 r d) :
    ∃ x y z : ℕ, d = demand3 r (first1 r) (second1 r) x y z ∧
      x ≤ y + z ∧ (x + y + z) % 2 = 0 := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb, hbe⟩ := hf
  rw [F1_inventory] at ha hbe
  have hn0 : ((d 0).toNat : ℤ) = d 0 := Int.toNat_of_nonneg (hn 0)
  have hn1 : ((d 1).toNat : ℤ) = d 1 := Int.toNat_of_nonneg (hn 1)
  have hn2 : ((d 2).toNat : ℤ) = d 2 := Int.toNat_of_nonneg (hn 2)
  have hn3 : ((d 3).toNat : ℤ) = d 3 := Int.toNat_of_nonneg (hn 3)
  refine ⟨(d r).toNat, (d (first1 r)).toNat, (d (second1 r)).toNat, ?_⟩
  have hnonneg := And.intro (hb {r, first1 r, first1 r})
    (hb {r, second1 r, second1 r})
  fin_cases r
  all_goals
    repeat rw [sum_insert (by decide)] at ha hbe
    have ha0 := congrFun ha 0
    have ha1 := congrFun ha 1
    have ha2 := congrFun ha 2
    have ha3 := congrFun ha 3
    have hb0 := congrFun hbe 0
    have hb1 := congrFun hbe 1
    have hb2 := congrFun hbe 2
    have hb3 := congrFun hbe 3
    norm_num [first1, second1, typeDegVec, sum_singleton] at ha0 ha1 ha2 ha3 ⊢
    norm_num [first1, second1, typeDegVec, sum_singleton,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hb0 hb1 hb2 hb3 hnonneg
    obtain ⟨hbn0, hbn1⟩ := hnonneg
    refine ⟨?_, ?_, ?_⟩
  all_goals
    first
    | (funext j; fin_cases j <;> simp [demand3, basis, hn0, hn1, hn2, hn3]; omega)
    | omega
    | (simp only [max_eq_left (hn _)]
       apply (Int.cast_le (R := ℝ)).mp
       push_cast
       linarith)

theorem F2_lower_coordinates (r : Fin 2) (d : Fin 4 → ℤ) (hn : ∀ j, 0 ≤ d j)
    (hi : LinkLattice F2 (lower2 r) d) (hf : LinkCone F2 (lower2 r) d) :
    ∃ x y z : ℕ, d = demand3 (lower2 r) 2 3 x y z ∧
      x ≤ y + z ∧ y ≤ x + z ∧ z ≤ x + y ∧ (x + y + z) % 2 = 0 := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb, hbe⟩ := hf
  rw [F2_lower_inventory] at ha hbe
  have hn0 : ((d 0).toNat : ℤ) = d 0 := Int.toNat_of_nonneg (hn 0)
  have hn1 : ((d 1).toNat : ℤ) = d 1 := Int.toNat_of_nonneg (hn 1)
  have hn2 : ((d 2).toNat : ℤ) = d 2 := Int.toNat_of_nonneg (hn 2)
  have hn3 : ((d 3).toNat : ℤ) = d 3 := Int.toNat_of_nonneg (hn 3)
  refine ⟨(d (lower2 r)).toNat, (d 2).toNat, (d 3).toNat, ?_⟩
  have hnonneg := And.intro (hb {lower2 r, lower2 r, 2})
    (And.intro (hb {lower2 r, lower2 r, 3}) (hb {lower2 r, 2, 3}))
  fin_cases r
  all_goals
    repeat rw [sum_insert (by decide)] at ha hbe
    have ha0 := congrFun ha 0
    have ha1 := congrFun ha 1
    have ha2 := congrFun ha 2
    have ha3 := congrFun ha 3
    have hb0 := congrFun hbe 0
    have hb1 := congrFun hbe 1
    have hb2 := congrFun hbe 2
    have hb3 := congrFun hbe 3
    norm_num [lower2, typeDegVec, sum_singleton] at ha0 ha1 ha2 ha3 ⊢
    norm_num [lower2, typeDegVec, sum_singleton, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hb0 hb1 hb2 hb3 hnonneg
    obtain ⟨hbn0, hbn1, hbn2⟩ := hnonneg
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | (funext j; fin_cases j <;> simp [demand3, basis, hn0, hn1, hn2, hn3]; omega)
    | omega
    | (simp only [max_eq_left (hn _)]
       apply (Int.cast_le (R := ℝ)).mp
       push_cast
       linarith)

theorem F2_upper_coordinates (r : Fin 2) (d : Fin 4 → ℤ) (hn : ∀ j, 0 ≤ d j)
    (hi : LinkLattice F2 (upper2 r) d) (hf : LinkCone F2 (upper2 r) d) :
    ∃ x y z : ℕ, d = demand3 (central2 r) 0 1 x y z ∧
      x ≤ y + z ∧ (x + y + z) % 2 = 0 := by
  obtain ⟨a, ha⟩ := hi
  obtain ⟨b, hb, hbe⟩ := hf
  rw [F2_upper_inventory] at ha hbe
  have hn0 : ((d 0).toNat : ℤ) = d 0 := Int.toNat_of_nonneg (hn 0)
  have hn1 : ((d 1).toNat : ℤ) = d 1 := Int.toNat_of_nonneg (hn 1)
  have hn2 : ((d 2).toNat : ℤ) = d 2 := Int.toNat_of_nonneg (hn 2)
  have hn3 : ((d 3).toNat : ℤ) = d 3 := Int.toNat_of_nonneg (hn 3)
  refine ⟨(d (central2 r)).toNat, (d 0).toNat, (d 1).toNat, ?_⟩
  have hnonneg := And.intro (hb {upper2 r, 0, 0}) (hb {upper2 r, 1, 1})
  fin_cases r
  all_goals
    repeat rw [sum_insert (by decide)] at ha hbe
    have ha0 := congrFun ha 0
    have ha1 := congrFun ha 1
    have ha2 := congrFun ha 2
    have ha3 := congrFun ha 3
    have hb0 := congrFun hbe 0
    have hb1 := congrFun hbe 1
    have hb2 := congrFun hbe 2
    have hb3 := congrFun hbe 3
    norm_num [upper2, central2, typeDegVec, sum_singleton] at ha0 ha1 ha2 ha3 ⊢
    norm_num [upper2, central2, typeDegVec, sum_singleton, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] at hb0 hb1 hb2 hb3 hnonneg
    obtain ⟨hbn0, hbn1⟩ := hnonneg
    refine ⟨?_, ?_, ?_⟩
  all_goals
    first
    | (funext j; fin_cases j <;> simp [demand3, basis, hn0, hn1, hn2, hn3]; omega)
    | omega
    | (simp only [max_eq_left (hn _)]
       apply (Int.cast_le (R := ℝ)).mp
       push_cast
       linarith)

variable {V : Type*} [DecidableEq V]

theorem degree_nonnegative (p : V → Fin 4) (P : Finset (Sym2 V)) (u : V) :
    ∀ j, 0 ≤ degVec p P u j := by
  intro j
  simp only [degVec, sum_apply]
  apply sum_nonneg
  intro e _
  induction e using Sym2.ind with
  | _ a b => simp only [degContrib, Sym2.lift_mk]; positivity

theorem F1_coordinates_of_divisibility (p : V → Fin 4) (P : Finset (Sym2 V))
    (hi : IsIntDiv p F1 P) (hf : IsFracDiv p F1 P) : F1Coordinates p P := by
  intro u
  exact F1_coordinates (p u) (degVec p P u) (degree_nonnegative p P u) (hi.2 u) (hf.2 u)

theorem F2_coordinates_of_divisibility (p : V → Fin 4) (P : Finset (Sym2 V))
    (hi : IsIntDiv p F2 P) (hf : IsFracDiv p F2 P) : F2Coordinates p P := by
  constructor
  · intro u r hr
    apply F2_lower_coordinates r (degVec p P u) (degree_nonnegative p P u)
    · simpa only [LinkLattice, hr] using hi.2 u
    · simpa only [LinkCone, hr] using hf.2 u
  · intro u r hr
    apply F2_upper_coordinates r (degVec p P u) (degree_nonnegative p P u)
    · simpa only [LinkLattice, hr] using hi.2 u
    · simpa only [LinkCone, hr] using hf.2 u

/-- Physical F1 link completion directly from the original divisibility predicates. -/
theorem F1_link_completion [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset)
    (α : ℝ) (hanti : AntiEdgeful p F1 G α)
    (hP : DegBounded P (α * Fintype.card V / 8))
    (hi : IsIntDiv p F1 P) (hf : IsFracDiv p F1 P)
    (q : ℕ) (hq : 0 < q) (hscale : 8 ≤ α * q)
    (hsize : 16 * ((q : ℝ) + 1) ≤ α * Fintype.card V) :
    ∃ R ⊆ G.edgeFinset, Disjoint P R ∧ DegBounded R (2 * (q + 1)) ∧
      HasDecomp p F1 R ∧ ∀ u, Realizable F1 (p u) (degVec p (P ∪ R) u) :=
  F1_physical_correction p G P hPG α hanti hP
    (F1_coordinates_of_divisibility p P hi hf) q hq hscale hsize

/-- Physical F2 link completion directly from the original divisibility predicates. -/
theorem F2_link_completion [Fintype V] (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Sym2 V)) (hPG : P ⊆ G.edgeFinset)
    (α : ℝ) (hanti : AntiEdgeful p F2 G α)
    (hP : DegBounded P (α * Fintype.card V / 8))
    (hi : IsIntDiv p F2 P) (hf : IsFracDiv p F2 P)
    (q : ℕ) (hq : 0 < q) (hscale : 8 ≤ α * q)
    (hsize : 16 * ((q : ℝ) + 1) ≤ α * Fintype.card V) :
    ∃ R ⊆ G.edgeFinset, Disjoint P R ∧ DegBounded R (2 * (q + 1)) ∧
      HasDecomp p F2 R ∧ ∀ u, Realizable F2 (p u) (degVec p (P ∪ R) u) :=
  F2_physical_correction p G P hPG α hanti hP
    (F2_coordinates_of_divisibility p P hi hf) q hq hscale hsize

end PartitionedTriangleAbsorption.TypedDivisibilityCoordinates
