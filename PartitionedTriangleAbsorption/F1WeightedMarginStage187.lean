/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1RootMassStage186
public import PartitionedTriangleAbsorption.TypedLoadNecessity

/-! # F1 host margin forced by the actual near-unit fractional loads

The root mass is counted in the host, and load error costs only the root
degree. This does not assume a margin on the graph after packing deletion.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1WeightedMarginStage187

open Finset TypedApplicationLinks F1RootCountsStage182 F1RootMassStage186 TypedLoadNecessity

variable {V : Type} [Fintype V] [DecidableEq V]

def charge (p : V → Fin 4) (v : V) (e : Sym2 V) : ℤ :=
  degContrib p v e (first1 (p v)) + degContrib p v e (second1 (p v)) -
    degContrib p v e (p v)

omit [Fintype V] in
theorem charge_triEdges (p : V → Fin 4) (s : Finset V)
    (hs : s.card = 3) (ht : triType p s ∈ F1) (v : V) :
    (∑ e ∈ triEdges s, charge p v e) =
      if v ∈ s ∧ (triType p s).count (p v) = 1 then 2 else 0 := by
  have hd := degVec_triEdges p hs v
  simp only [charge, sum_sub_distrib, sum_add_distrib]
  have hdf (j : Fin 4) := congrFun hd j
  simp only [degVec, Finset.sum_apply] at hdf
  rw [hdf, hdf, hdf]
  by_cases hv : v ∈ s
  · simpa [hv] using F1_root_charge _ ht _ (mem_triType hv)
  · simp [hv]

theorem weighted_root_identity (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (φ : Finset V → ℝ) (v : V) :
    (∑ e ∈ G.edgeFinset, (charge p v e : ℝ) * edgeLoad p F1 G φ e) =
      2 * ∑ s ∈ singletonFamily p (copies p F1 G) v, φ s := by
  rw [sum_mul_edgeLoad]
  have heq : (∑ s ∈ copies p F1 G, φ s * ∑ e ∈ triEdges s, (charge p v e : ℝ)) =
      ∑ s ∈ copies p F1 G,
        if v ∈ s ∧ (triType p s).count (p v) = 1 then 2 * φ s else 0 := by
    apply sum_congr rfl
    intro s hs
    have hc := TypedNibble.mem_copies_iff.mp hs
    rw [← Int.cast_sum, charge_triEdges p s hc.1.card_eq hc.2 v]
    split_ifs <;> simp [mul_comm]
  rw [heq, ← sum_filter, ← mul_sum]
  rfl

omit [Fintype V] in
theorem abs_charge_le (p : V → Fin 4) (v : V) (e : Sym2 V) (he : ¬ e.IsDiag) :
    |charge p v e| ≤ if v ∈ e then 1 else 0 := by
  have hlabel : ∀ r l : Fin 4,
      |(if l = first1 r then (1 : ℤ) else 0) +
        (if l = second1 r then 1 else 0) - (if l = r then 1 else 0)| ≤ 1 := by decide
  induction e using Sym2.ind with
  | _ a b =>
    have hab : a ≠ b := fun h => he (Sym2.mk_isDiag_iff.mpr h)
    by_cases ha : a = v
    · subst a
      simpa [charge, degContrib, hab.symm] using hlabel (p v) (p b)
    · by_cases hb : b = v
      · subst b
        simpa [charge, degContrib, ha] using hlabel (p v) (p a)
      · simp [charge, degContrib, ha, hb, Ne.symm ha, Ne.symm hb]

theorem margin_error (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (φ : Finset V → ℝ) (v : V) (ε : ℝ) (hε : 0 ≤ ε)
    (hload : ∀ e ∈ G.edgeFinset, |edgeLoad p F1 G φ e - 1| ≤ ε) :
    |(surplus p G.edgeFinset v : ℝ) -
      2 * ∑ s ∈ singletonFamily p (copies p F1 G) v, φ s| ≤ ε * Fintype.card V := by
  have hsum : (∑ e ∈ G.edgeFinset, (charge p v e : ℝ)) =
      (surplus p G.edgeFinset v : ℝ) := by
    rw [← Int.cast_sum]
    congr 1
    simp only [charge, surplus, degVec, Finset.sum_apply, sum_sub_distrib, sum_add_distrib]
  have hid : (surplus p G.edgeFinset v : ℝ) -
      2 * ∑ s ∈ singletonFamily p (copies p F1 G) v, φ s =
      ∑ e ∈ G.edgeFinset, (charge p v e : ℝ) * (1 - edgeLoad p F1 G φ e) := by
    rw [← hsum, ← weighted_root_identity p G φ v, ← sum_sub_distrib]
    apply sum_congr rfl
    intro e _
    ring
  have hterm : ∀ e ∈ G.edgeFinset,
      |(charge p v e : ℝ) * (1 - edgeLoad p F1 G φ e)| ≤
        ε * (if v ∈ e then (1 : ℝ) else 0) := by
    intro e he
    have hc : |(charge p v e : ℝ)| ≤ if v ∈ e then (1 : ℝ) else 0 := by
      exact_mod_cast abs_charge_le p v e
        (G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he))
    have hl : |1 - edgeLoad p F1 G φ e| ≤ ε := by
      rw [abs_sub_comm]
      exact hload e he
    rw [abs_mul]
    have h := mul_le_mul hc hl (abs_nonneg _) (by split_ifs <;> norm_num)
    simpa [mul_comm] using h
  have hcard : ((G.edgeFinset.filter fun e => v ∈ e).card : ℝ) ≤ Fintype.card V := by
    rw [← G.incidenceFinset_eq_filter, G.card_incidenceFinset_eq_degree]
    exact_mod_cast (G.degree_lt_card_verts v).le
  rw [hid]
  calc
    _ ≤ ∑ e ∈ G.edgeFinset, |(charge p v e : ℝ) * (1 - edgeLoad p F1 G φ e)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ G.edgeFinset, ε * (if v ∈ e then (1 : ℝ) else 0) := sum_le_sum hterm
    _ = ε * ((G.edgeFinset.filter fun e => v ∈ e).card : ℝ) := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [← sum_filter]
      simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hcard hε

theorem strict_host_margin (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (α ε b : ℝ) (hα : 0 ≤ α) (hε0 : 0 ≤ ε)
    (hε : ε ≤ α / 4) (hb : 0 < b) (hn : 0 < Fintype.card V)
    (hsize : α * Fintype.card V ≤
      ((univ.filter fun x => p x = first1 (p v)).card : ℝ))
    (hmissRoot : ((univ.filter fun x => p x = first1 (p v) ∧ ¬ G.Adj v x).card : ℝ) ≤
      ε * Fintype.card V)
    (hmissClass : ∀ x, p x = first1 (p v) →
      ((univ.filter fun y => p y = first1 (p v) ∧ ¬ G.Adj x y).card : ℝ) ≤
        ε * Fintype.card V)
    (φ : Finset V → ℝ)
    (hw : ∀ s, IsCopy p F1 G s → 1 / (b * Fintype.card V) ≤ φ s)
    (hload : ∀ e ∈ G.edgeFinset, |edgeLoad p F1 G φ e - 1| ≤ ε) :
    (α ^ 2 / (18 * b) - ε) * Fintype.card V ≤ (surplus p G.edgeFinset v : ℝ) := by
  have hm := singleton_fractional_mass p G v α ε b hα hε hb hn hsize hmissRoot hmissClass φ hw
  have he := (abs_le.mp (margin_error p G φ v ε hε0 hload)).1
  have hfrac : α ^ 2 / (18 * b) = 2 * (α ^ 2 / (36 * b)) := by ring
  rw [hfrac]
  linarith

end PartitionedTriangleAbsorption.F1WeightedMarginStage187

