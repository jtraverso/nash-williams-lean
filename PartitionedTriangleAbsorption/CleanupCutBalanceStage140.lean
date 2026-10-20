/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.MatchedQuotaStage140

/-! # The three matching cuts determine the F3 balances

This is a physical counting identity. Equal residual cut counts give the two
opposite-pair edge-count balances required by the four-colour consumer.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CleanupCutBalanceStage140

open Finset MatchedQuotaStage140

variable {V : Type*}

def opposite (p : V → Fin 4) (E : Finset (Sym2 V)) (i : Fin 3) : ℤ :=
  if i = 0 then edgeVec p E 0 1 + edgeVec p E 2 3
  else if i = 1 then edgeVec p E 0 2 + edgeVec p E 1 3
  else edgeVec p E 0 3 + edgeVec p E 1 2

theorem cut_add_opposite (p : V → Fin 4) (E : Finset (Sym2 V)) (i : Fin 3) :
    ((cuts p E i).card : ℤ) + opposite p E i =
      ((E.filter fun e => ¬ (e.map p).IsDiag).card : ℤ) := by
  have hc (f : Sym2 V → Prop) [DecidablePred f] :
      ((E.filter f).card : ℤ) = ∑ e ∈ E, if f e then (1 : ℤ) else 0 := by
    rw [← sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
  rw [cuts, hc, hc]
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  fin_cases i <;>
    simp only [opposite, Fin.reduceFinMk, h10, h20, h21, ↓reduceIte, edgeVec,
      Finset.sum_apply, ← sum_add_distrib] <;>
    apply sum_congr rfl <;>
    intro e _ <;>
    induction e using Sym2.ind with
    | _ a b =>
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff, Function.comp_apply,
        pairVec, Sym2.lift_mk]
      generalize p a = x
      generalize p b = y
      fin_cases x <;> fin_cases y <;> decide

theorem balances_of_equal_cuts (p : V → Fin 4) (E : Finset (Sym2 V))
    (h01 : (cuts p E 0).card = (cuts p E 1).card)
    (h02 : (cuts p E 0).card = (cuts p E 2).card) :
    (edgeVec p E 0 1 + edgeVec p E 2 3 = edgeVec p E 0 2 + edgeVec p E 1 3) ∧
    (edgeVec p E 0 1 + edgeVec p E 2 3 = edgeVec p E 0 3 + edgeVec p E 1 2) := by
  have h0 := cut_add_opposite p E 0
  have h1 := cut_add_opposite p E 1
  have h2 := cut_add_opposite p E 2
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  simp only [opposite, h10, h20, h21, ↓reduceIte] at h0 h1 h2
  rw [← h01] at h1
  rw [← h02] at h2
  constructor <;> omega

end PartitionedTriangleAbsorption.CleanupCutBalanceStage140
