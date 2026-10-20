/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F3ReserveTrimStage109
public import PartitionedTriangleAbsorption.TypedLoadNecessity

/-! # Actual category surplus from approximate physical edge loads

The surplus is derived from the seed on the same host. It is not a
separately supplied bound on the outcome of a vertex sample.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ApproximateBalanceStage114

open Finset TypedNibble TypedApplicationLinks TypedLoadNecessity
  CoverDownStage105 F3ReserveTrimStage109 ReserveTrimStage109

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] [DecidableEq V] in
theorem balEdge_abs_le_one (p : V → Fin 4) (k : Fin 2) (e : Sym2 V) :
    |(balEdge p k e : ℝ)| ≤ 1 := by
  have ht : ∀ (k : Fin 2) (i j : Fin 4), |balTab k i j| ≤ 1 := by decide
  induction e using Sym2.ind with
  | _ u v =>
    simp only [balEdge, Sym2.lift_mk]
    exact_mod_cast ht k (p u) (p v)

theorem balance_bound (p : V → Fin 4) (J : SimpleGraph V) [DecidableRel J.Adj]
    (φ : Finset V → ℝ) (ε : ℝ)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε) (k : Fin 2) :
    |(bal p k J.edgeFinset : ℝ)| ≤ ε * J.edgeFinset.card := by
  have hz : (∑ e ∈ J.edgeFinset, (balEdge p k e : ℝ) * edgeLoad p F3 J φ e) = 0 := by
    rw [sum_mul_edgeLoad]
    apply sum_eq_zero
    intro s hs
    have ht := bal_triEdges p k (isTypedTri_of_isCopy (mem_copies_iff.mp hs))
    have htR : (∑ e ∈ triEdges s, (balEdge p k e : ℝ)) = 0 := by
      exact_mod_cast ht
    rw [htR, mul_zero]
  have hid : (bal p k J.edgeFinset : ℝ) =
      ∑ e ∈ J.edgeFinset, (balEdge p k e : ℝ) * (1 - edgeLoad p F3 J φ e) := by
    simp only [bal, Int.cast_sum, mul_sub, mul_one, sum_sub_distrib, hz, sub_zero]
  rw [hid]
  calc
    _ ≤ ∑ e ∈ J.edgeFinset, |(balEdge p k e : ℝ) * (1 - edgeLoad p F3 J φ e)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ J.edgeFinset, ε := by
      apply sum_le_sum
      intro e he
      rw [abs_mul]
      have heps : |1 - edgeLoad p F3 J φ e| ≤ ε := by
        simpa only [abs_sub_comm] using hload e he
      simpa using mul_le_mul (balEdge_abs_le_one p k e) heps (abs_nonneg _) (by norm_num)
    _ = ε * J.edgeFinset.card := by simp [mul_comm]

/-- Every pair of category counts differs by at most twice the load error
times the number of physical edges. -/
theorem category_difference (p : V → Fin 4) (J : SimpleGraph V)
    [DecidableRel J.Adj] (φ : Finset V → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hcross : ∀ u v, J.Adj u v → p u ≠ p v)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε) (i j : Fin 3) :
    |((pool (category p) J.edgeFinset i).card : ℝ) -
      (pool (category p) J.edgeFinset j).card| ≤ 2 * ε * J.edgeFinset.card := by
  let a := fun i => ((pool (category p) J.edgeFinset i).card : ℝ)
  have hbase : ∀ i : Fin 3, |a 0 - a i| ≤ ε * J.edgeFinset.card := by
    intro i
    have hb := fun k => balance_bound p J φ ε hload k
    have hcross' : ∀ u v, s(u, v) ∈ J.edgeFinset → p u ≠ p v :=
      fun u v he => hcross u v (SimpleGraph.mem_edgeFinset.mp he)
    have h0 := bal_eq_category_counts p (0 : Fin 2) J.edgeFinset hcross'
    have h1 := bal_eq_category_counts p (1 : Fin 2) J.edgeFinset hcross'
    fin_cases i
    · change |a 0 - a 0| ≤ _
      rw [sub_self, abs_zero]
      positivity
    · have h := hb 0
      rw [h0] at h
      simpa [a] using h
    · have h := hb 1
      rw [h1] at h
      simpa [a] using h
  change |a i - a j| ≤ _
  have hi : |a i - a 0| ≤ ε * J.edgeFinset.card := by
    simpa only [abs_sub_comm] using hbase i
  have h := (abs_sub_le (a i) (a 0) (a j)).trans (add_le_add hi (hbase j))
  nlinarith

end PartitionedTriangleAbsorption.ApproximateBalanceStage114
