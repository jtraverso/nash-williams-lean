/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.ReturnedBasic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega

/-! The edge count used by the greedy apex budget counts unordered edges
twice in the vertex-degree sum, without a loss of a factor two. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset

theorem leftover_incidence_sum {V : Type*} [Fintype V] [DecidableEq V]
    (L : Finset (Sym2 V)) (hloop : ∀ e ∈ L, ¬ e.IsDiag) :
    ∑ v : V, (L.filter (fun e => v ∈ e)).card = 2 * L.card := by
  simp_rw [card_filter]
  rw [sum_comm]
  have hterm : ∀ e ∈ L, (∑ v : V, if v ∈ e then 1 else 0) = (2 : ℕ) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
      have hab : a ≠ b := by simpa using hloop _ he
      have heq : univ.filter (fun v : V => v ∈ s(a, b)) = {a, b} := by
        ext v
        simp [Sym2.mem_iff]
      rw [← card_filter, heq, card_pair hab]
  rw [sum_congr rfl hterm]
  simp [mul_comm]

theorem twice_leftover_card_le {V : Type*} [Fintype V] [DecidableEq V]
    (L : Finset (Sym2 V)) (hloop : ∀ e ∈ L, ¬ e.IsDiag) (D : ℕ)
    (hD : ∀ v, (L.filter (fun e => v ∈ e)).card ≤ D) :
    2 * L.card ≤ Fintype.card V * D := by
  rw [← leftover_incidence_sum L hloop]
  calc
    _ ≤ ∑ _v : V, D := sum_le_sum fun v _ => hD v
    _ = _ := by simp

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.leftover_incidence_sum
#print axioms NashWilliams18.Case124.BoundedCore.twice_leftover_card_le
