/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FourClassChargeBridgeStage75
public import Mathlib.Tactic.FinCases

/-! # The two integral charges governing four-class reserve neutrality

The symmetric ordered-edge bookkeeping contributes a factor of two. Removing
that factor makes the correction requests integral, and the annihilator lemma
shows that cancelling these two charges cancels every F3 type functional.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.NeutralChargeStage76

open Finset TypedLoadNecessity FourClassChargeBridgeStage75

variable {V : Type*}

def aEdge (p : V → Fin 4) (e : Sym2 V) : ℤ :=
  pairFun TypedRefinerCharge.chi3a (pairVec p e) / 2

def bEdge (p : V → Fin 4) (e : Sym2 V) : ℤ :=
  pairFun TypedRefinerCharge.chi3b (pairVec p e) / 2

theorem aEdge_mk (p : V → Fin 4) (u v : V) :
    aEdge p s(u,v) = TypedRefinerCharge.chi3a (p u) (p v) := by
  rw [aEdge, pairFun_mk]
  generalize p u = i, p v = j
  fin_cases i <;> fin_cases j <;> decide

theorem bEdge_mk (p : V → Fin 4) (u v : V) :
    bEdge p s(u,v) = TypedRefinerCharge.chi3b (p u) (p v) := by
  rw [bEdge, pairFun_mk]
  generalize p u = i, p v = j
  fin_cases i <;> fin_cases j <;> decide

theorem edge_bounds (p : V → Fin 4) (e : Sym2 V) :
    |aEdge p e| ≤ 1 ∧ |bEdge p e| ≤ 1 := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [aEdge_mk, bEdge_mk]
    exact ⟨TypedRefinerCharge.chi3a_bound _ _, TypedRefinerCharge.chi3b_bound _ _⟩

def a (p : V → Fin 4) (X : Finset (Sym2 V)) : ℤ := ∑ e ∈ X, aEdge p e
def b (p : V → Fin 4) (X : Finset (Sym2 V)) : ℤ := ∑ e ∈ X, bEdge p e

theorem charge_bounds (p : V → Fin 4) (X : Finset (Sym2 V)) :
    |a p X| ≤ X.card ∧ |b p X| ≤ X.card := by
  constructor
  · exact (abs_sum_le_sum_abs _ _).trans (by
      calc ∑ e ∈ X, |aEdge p e| ≤ ∑ _e ∈ X, (1 : ℤ) :=
            sum_le_sum fun e _ => (edge_bounds p e).1
        _ = X.card := by simp)
  · exact (abs_sum_le_sum_abs _ _).trans (by
      calc ∑ e ∈ X, |bEdge p e| ≤ ∑ _e ∈ X, (1 : ℤ) :=
            sum_le_sum fun e _ => (edge_bounds p e).2
        _ = X.card := by simp)

theorem correction_counts (p : V → Fin 4) (X : Finset (Sym2 V)) :
    ∃ m01 m02 m03 : ℕ, m01 ≤ 2 * X.card ∧ m02 ≤ 2 * X.card ∧
      m03 ≤ 2 * X.card ∧
      a p X + m01 - m02 = 0 ∧ b p X + m01 - m03 = 0 := by
  obtain ⟨ha,hb⟩ := charge_bounds p X
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  let t : ℤ := max 0 (max (-a p X) (-b p X))
  have ht : 0 ≤ t := le_max_left _ _
  have hta : -a p X ≤ t := (le_max_left _ _).trans (le_max_right _ _)
  have htb : -b p X ≤ t := (le_max_right _ _).trans (le_max_right _ _)
  have htcard : t ≤ X.card := max_le (by positivity) (max_le (by omega) (by omega))
  refine ⟨t.toNat, (a p X + t).toNat, (b p X + t).toNat, ?_, ?_, ?_, ?_, ?_⟩
  all_goals omega

theorem annihilator_coefficients (l : Fin 4 → Fin 4 → ℤ)
    (hl : Annihilates TypedApplicationLinks.F3 l) :
    (l 0 1 + l 1 0) = (l 2 3 + l 3 2) ∧
    (l 0 2 + l 2 0) = (l 1 3 + l 3 1) ∧
    (l 0 3 + l 3 0) = (l 1 2 + l 2 1) ∧
    (l 0 1 + l 1 0) + (l 0 2 + l 2 0) + (l 0 3 + l 3 0) = 0 := by
  have h012 := hl {0,1,2} (by decide)
  have h013 := hl {0,1,3} (by decide)
  have h023 := hl {0,2,3} (by decide)
  have h123 := hl {1,2,3} (by decide)
  norm_num [pairFun, typeEdgeVec, Fin.sum_univ_succ] at h012 h013 h023 h123
  omega

theorem annihilator_edge (l : Fin 4 → Fin 4 → ℤ)
    (hl : Annihilates TypedApplicationLinks.F3 l) (p : V → Fin 4)
    (u v : V) (huv : p u ≠ p v) :
    pairFun l (pairVec p s(u,v)) =
      -(l 0 2 + l 2 0) * aEdge p s(u,v) - (l 0 3 + l 3 0) * bEdge p s(u,v) := by
  obtain ⟨h1,h2,h3,h4⟩ := annihilator_coefficients l hl
  rw [pairFun_mk, aEdge_mk, bEdge_mk]
  generalize hi : p u = i at *
  generalize hj : p v = j at *
  fin_cases i <;> fin_cases j <;>
    norm_num [TypedRefinerCharge.chi3a, TypedRefinerCharge.chi3b] at * <;> omega

theorem neutral_of_two_charges (p : V → Fin 4) (X : Finset (Sym2 V))
    (hcross : ∀ e ∈ X, ∀ u v, e = s(u, v) → p u ≠ p v)
    (ha : a p X = 0) (hb : b p X = 0)
    (l : Fin 4 → Fin 4 → ℤ) (hl : Annihilates TypedApplicationLinks.F3 l) :
    ∑ e ∈ X, pairFun l (pairVec p e) = 0 := by
  have he : ∀ e ∈ X, pairFun l (pairVec p e) =
      -(l 0 2 + l 2 0) * aEdge p e - (l 0 3 + l 3 0) * bEdge p e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v => exact annihilator_edge l hl p u v (hcross _ he _ _ rfl)
  rw [sum_congr rfl he]
  simp only [sum_sub_distrib, ← mul_sum]
  change -(l 0 2 + l 2 0) * a p X - (l 0 3 + l 3 0) * b p X = 0
  rw [ha, hb, mul_zero, mul_zero, sub_self]

end PartitionedTriangleAbsorption.NeutralChargeStage76
