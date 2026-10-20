/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IntegerCertificate.Combination
public import Mathlib.Algebra.BigOperators.Fin

/-! # The two numerical consequences of `IsIntDiv p F0 P`

For a loopless edge set `P` (in particular for `P ⊆ G.edgeFinset`):

* `even_degree_of_isIntDiv`: every vertex has even degree in `P` — every F0 type degree
  vector has coordinate sum `2`;
* `charge_ind_of_isIntDiv`: the F0 charge `crossing - 2·internal` of `P` vanishes — it
  vanishes on both F0 type edge vectors.

These are proved against the actual ordered-vector conventions of `IsIntDiv`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.IntegerCertificate

open Finset SignedCertificate TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V] {p : V → Fin 2}

/-- Degree of `y` in the edge set `P`. -/
def deg (P : Finset (Sym2 V)) (y : V) : ℕ := (P.filter (y ∈ ·)).card

omit [Fintype V] in
theorem sum_degContrib (y : V) {e : Sym2 V} (he : ¬ e.IsDiag) :
    ∑ i, degContrib p y e i = if y ∈ e then 1 else 0 := by
  induction e using Sym2.ind with
  | _ a b =>
  have hab : a ≠ b := by simpa using he
  have key : ∀ c d : V, ∑ i, (if c = y ∧ p d = i then (1 : ℤ) else 0) =
      if c = y then 1 else 0 := by
    intro c d
    by_cases h : c = y
    · simp [h]
    · simp [h]
  simp only [degContrib, Sym2.lift_mk, sum_add_distrib, key, Sym2.mem_iff]
  by_cases ha : a = y <;> by_cases hb : b = y
  · exact absurd (ha.trans hb.symm) hab
  · simp [ha, hb]
  · simp [ha, hb]
  · simp [ha, hb, Ne.symm ha, Ne.symm hb]

theorem typeDegVec_sum_F0 : ∀ τ ∈ F0, ∀ a : Fin 2, ∑ i, typeDegVec τ a i = 2 := by
  intro τ hτ a
  simp only [F0, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl <;> fin_cases a <;> simp [typeDegVec, Fin.sum_univ_two]

omit [Fintype V] in
/-- **Even degree.** Integral F0-divisibility of a loopless edge set forces every degree to be
even. -/
theorem even_degree_of_isIntDiv {P : Finset (Sym2 V)} (h : IsIntDiv p F0 P)
    (hP : ∀ e ∈ P, ¬ e.IsDiag) (y : V) : ∃ k : ℕ, deg P y = 2 * k := by
  obtain ⟨c, hc⟩ := h.2 y
  have lhs : ∑ i, degVec p P y i = (deg P y : ℤ) := by
    simp only [degVec, sum_apply]
    rw [sum_comm, sum_congr rfl fun e he => sum_degContrib (p := p) y (hP e he), sum_boole]
    rfl
  have rhs : ∑ i, (∑ τ ∈ F0 with p y ∈ τ, c τ • typeDegVec τ (p y)) i =
      2 * ∑ τ ∈ F0 with p y ∈ τ, c τ := by
    simp only [sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun τ hτ => ?_
    rw [← mul_sum, typeDegVec_sum_F0 τ (mem_filter.mp hτ).1, mul_comm]
  rw [hc, rhs] at lhs
  have h0 : 0 ≤ ∑ τ ∈ F0 with p y ∈ τ, c τ := by omega
  refine ⟨(∑ τ ∈ F0 with p y ∈ τ, c τ).toNat, ?_⟩
  omega

omit [Fintype V] [DecidableEq V] in
theorem kappa_eq_pairVec (e : Sym2 V) :
    kappa p e = pairVec p e 0 1 - pairVec p e 0 0 - pairVec p e 1 1 := by
  induction e using Sym2.ind with
  | _ a b =>
  simp only [kappa, pairVec, Sym2.lift_mk]
  generalize p a = x; generalize p b = y
  revert x y; decide

theorem typeEdgeVec_charge_F0 : ∀ τ ∈ F0,
    typeEdgeVec τ 0 1 - typeEdgeVec τ 0 0 - typeEdgeVec τ 1 1 = 0 := by
  intro τ hτ
  simp only [F0, mem_insert, mem_singleton] at hτ
  rcases hτ with rfl | rfl <;> simp [typeEdgeVec]

/-- **Zero charge.** Integral F0-divisibility forces `crossing - 2·internal = 0`. -/
theorem charge_ind_of_isIntDiv {P : Finset (Sym2 V)} (h : IsIntDiv p F0 P) :
    charge p (ind P) = 0 := by
  obtain ⟨c, hc⟩ := h.1
  have h1 : charge p (ind P) = edgeVec p P 0 1 - edgeVec p P 0 0 - edgeVec p P 1 1 := by
    rw [charge, sum_congr rfl fun e _ => mul_comm _ _, ← sum_eq_sum_ind P (kappa p)]
    simp only [edgeVec, sum_apply, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => kappa_eq_pairVec e
  rw [h1, hc]
  simp only [sum_apply, Pi.smul_apply, smul_eq_mul, ← sum_sub_distrib]
  refine sum_eq_zero fun τ hτ => ?_
  rw [← mul_sub, ← mul_sub, typeEdgeVec_charge_F0 τ hτ, mul_zero]

end PartitionedTriangleAbsorption.IntegerCertificate
