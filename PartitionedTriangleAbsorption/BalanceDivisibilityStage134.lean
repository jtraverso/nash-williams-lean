/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveAwareRecutStage120

/-! # Stage134: integral F3-divisibility forces zero type balance

The two balance functionals are linear functionals of the edge-count vector
which vanish on every F3 type. Hence actual integral divisibility of a host
gives its zero balance; balance is never an extra hypothesis of a level.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BalanceDivisibilityStage134

open Finset TypedApplicationLinks CoverDownStage105

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The balance functional on edge-count vectors. -/
def balFun (k : Fin 2) (M : Fin 4 → Fin 4 → ℤ) : ℤ :=
  if k = 0 then M 0 1 + M 2 3 - M 0 2 - M 1 3 else M 0 1 + M 2 3 - M 0 3 - M 1 2

theorem balFun_add (k : Fin 2) (M N : Fin 4 → Fin 4 → ℤ) :
    balFun k (M + N) = balFun k M + balFun k N := by
  unfold balFun; split_ifs <;> simp only [Pi.add_apply] <;> ring

theorem balFun_smul (k : Fin 2) (c : ℤ) (M : Fin 4 → Fin 4 → ℤ) :
    balFun k (c • M) = c * balFun k M := by
  unfold balFun; split_ifs <;> simp only [Pi.smul_apply, smul_eq_mul] <;> ring

theorem balFun_sum {ι : Type*} (k : Fin 2) (s : Finset ι) (f : ι → Fin 4 → Fin 4 → ℤ) :
    balFun k (∑ i ∈ s, f i) = ∑ i ∈ s, balFun k (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [balFun]
  | insert a s ha ih => rw [sum_insert ha, sum_insert ha, balFun_add, ih]

omit [Fintype V] [DecidableEq V] in
theorem balEdge_eq_balFun (p : V → Fin 4) (k : Fin 2) (e : Sym2 V) :
    balEdge p k e = balFun k (pairVec p e) := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [balEdge, pairVec, Sym2.lift_mk]
    generalize p a = i
    generalize p b = j
    revert k i j
    decide

theorem balFun_type (k : Fin 2) : ∀ τ ∈ F3, balFun k (typeEdgeVec τ) = 0 := by
  revert k; decide

omit [Fintype V] [DecidableEq V] in
theorem bal_eq_balFun (p : V → Fin 4) (k : Fin 2) (E : Finset (Sym2 V)) :
    bal p k E = balFun k (edgeVec p E) := by
  unfold bal edgeVec
  rw [balFun_sum]
  exact sum_congr rfl fun e _ => balEdge_eq_balFun p k e

omit [Fintype V] in
/-- **Integral F3-divisibility gives zero balance.** -/
theorem bal_zero_of_isIntDiv (p : V → Fin 4) {E : Finset (Sym2 V)}
    (h : IsIntDiv p F3 E) : ∀ k : Fin 2, bal p k E = 0 := by
  intro k
  obtain ⟨⟨c, hc⟩, -⟩ := h
  rw [bal_eq_balFun, hc, balFun_sum]
  exact sum_eq_zero fun τ hτ => by rw [balFun_smul, balFun_type k τ hτ, mul_zero]

end PartitionedTriangleAbsorption.BalanceDivisibilityStage134
