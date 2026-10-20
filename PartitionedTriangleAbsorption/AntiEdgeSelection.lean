/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-! # Select typed anti-edges away from used edges and saturated vertices

This deterministic step consumes the unchanged `AntiEdgeful` hypothesis.
It does not construct a universal reserve or an omniabsorber, and requires
an explicit congestion budget rather than assuming fresh vertices exist.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.AntiEdgeSelection

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

def blockedNeighbours (B : Finset (Sym2 V)) (u : V) : Finset V :=
  univ.filter (fun w => s(u, w) ∈ B)

def incidentLoad (B : Finset (Sym2 V)) (u : V) : ℕ :=
  (B.filter (fun e => u ∈ e)).card

/-- Blocking an endpoint removes at most its incident used-edge count. -/
theorem blockedNeighbours_card_le (B : Finset (Sym2 V)) (u : V) :
    (blockedNeighbours B u).card ≤ incidentLoad B u := by
  apply Finset.card_le_card_of_injOn (fun w => s(u, w))
  · intro w hw
    exact mem_filter.mpr ⟨(mem_filter.mp hw).2, by simp [Sym2.mem_iff]⟩
  · intro a _ b _ hab
    rcases Sym2.eq_iff.mp hab with ⟨_, hab⟩ | ⟨hub, hau⟩
    · exact hab
    · exact hau.trans hub

/-- Union-bound budget over actual candidate vertices and physical blocked edges. -/
theorem available_card_budget (W Z : Finset V) (B : Finset (Sym2 V)) (u v : V) :
    W.card ≤ (W \ (Z ∪ blockedNeighbours B u ∪ blockedNeighbours B v)).card +
      Z.card + incidentLoad B u + incidentLoad B v := by
  let bad := Z ∪ blockedNeighbours B u ∪ blockedNeighbours B v
  have hsub : W ⊆ (W \ bad) ∪ bad := by
    intro w hw
    by_cases hb : w ∈ bad
    · exact mem_union.mpr (Or.inr hb)
    · exact mem_union.mpr (Or.inl (mem_sdiff.mpr ⟨hw, hb⟩))
  have hb : bad.card ≤ Z.card + incidentLoad B u + incidentLoad B v :=
    (card_union_le _ _).trans (Nat.add_le_add
      ((card_union_le _ _).trans (Nat.add_le_add_left (blockedNeighbours_card_le B u) _))
      (blockedNeighbours_card_le B v))
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  exact hc.trans (by simpa only [Nat.add_assoc] using Nat.add_le_add_left hb (W \ bad).card)

/-- Typed common-neighbour supply survives exclusion under an explicit strict budget.
The original pair `uv` need not be an edge: this selects an anti-edge, not a copy of `G`. -/
theorem exists_avoiding (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (α : ℝ)
    (hanti : AntiEdgeful p F G α) (i j k : Fin t)
    (hτ : ({i, j, k} : Multiset (Fin t)) ∈ F)
    (u v : V) (huv : u ≠ v) (hu : p u = i) (hv : p v = j)
    (B : Finset (Sym2 V)) (Z : Finset V)
    (hbudget : (Z.card + incidentLoad B u + incidentLoad B v : ℕ) <
      α * (Fintype.card V : ℝ)) :
    ∃ w, G.Adj u w ∧ G.Adj w v ∧ p w = k ∧ w ∉ Z ∧
      s(u, w) ∉ B ∧ s(v, w) ∉ B := by
  let W := univ.filter (fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k)
  let good := W \ (Z ∪ blockedNeighbours B u ∪ blockedNeighbours B v)
  have hlarge : α * (Fintype.card V : ℝ) ≤ (W.card : ℝ) :=
    hanti {i, j, k} hτ i j k rfl u v huv hu hv
  have hcount := available_card_budget W Z B u v
  have hnonempty : good.Nonempty := by
    apply card_pos.mp
    by_contra h
    have hzero : good.card = 0 := by omega
    have hsmall : W.card ≤ Z.card + incidentLoad B u + incidentLoad B v := by
      simpa only [show (W \ (Z ∪ blockedNeighbours B u ∪ blockedNeighbours B v)).card = 0
        from hzero, Nat.zero_add] using hcount
    have hsmallReal : (W.card : ℝ) ≤ (Z.card + incidentLoad B u + incidentLoad B v : ℕ) :=
      by exact_mod_cast hsmall
    exact (not_lt_of_ge (hlarge.trans hsmallReal)) hbudget
  obtain ⟨w, hw⟩ := hnonempty
  have hW := (mem_filter.mp (mem_sdiff.mp hw).1).2
  have hbad := (mem_sdiff.mp hw).2
  refine ⟨w, hW.1, hW.2.1, hW.2.2, ?_, ?_, ?_⟩
  · intro hz
    exact hbad (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl hz))))
  · intro he
    exact hbad (mem_union.mpr (Or.inl (mem_union.mpr
      (Or.inr (mem_filter.mpr ⟨mem_univ w, he⟩)))))
  · intro he
    exact hbad (mem_union.mpr (Or.inr (mem_filter.mpr ⟨mem_univ w, he⟩)))

/-- Uniform used-edge degree bound reduces the exclusion budget to `|Z|+2d`. -/
theorem exists_avoiding_of_degree_bound (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (α d : ℝ)
    (hanti : AntiEdgeful p F G α) (i j k : Fin t)
    (hτ : ({i, j, k} : Multiset (Fin t)) ∈ F)
    (u v : V) (huv : u ≠ v) (hu : p u = i) (hv : p v = j)
    (B : Finset (Sym2 V)) (Z : Finset V) (hB : DegBounded B d)
    (hbudget : (Z.card : ℝ) + 2 * d < α * (Fintype.card V : ℝ)) :
    ∃ w, G.Adj u w ∧ G.Adj w v ∧ p w = k ∧ w ∉ Z ∧
      s(u, w) ∉ B ∧ s(v, w) ∉ B := by
  apply exists_avoiding p F G α hanti i j k hτ u v huv hu hv B Z
  have hBu : (incidentLoad B u : ℝ) ≤ d := hB u
  have hBv : (incidentLoad B v : ℝ) ≤ d := hB v
  push_cast
  linarith

omit [DecidableEq V] in
/-- A saturated-vertex count is controlled by the total auxiliary load. -/
theorem saturated_card_budget (load : V → ℕ) (q : ℕ) :
    q * (univ.filter (fun v => q ≤ load v)).card ≤ ∑ v, load v := by
  classical
  calc
    q * (univ.filter (fun v => q ≤ load v)).card =
        ∑ _v ∈ univ.filter (fun v => q ≤ load v), q := by simp [Nat.mul_comm]
    _ ≤ ∑ v ∈ univ.filter (fun v => q ≤ load v), load v :=
      sum_le_sum fun _ hv => (mem_filter.mp hv).2
    _ ≤ ∑ v, load v := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by simp)

/-- A local greedy step avoiding used edges and all saturated auxiliary vertices. -/
theorem exists_unsaturated (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (α d : ℝ)
    (hanti : AntiEdgeful p F G α) (i j k : Fin t)
    (hτ : ({i, j, k} : Multiset (Fin t)) ∈ F)
    (u v : V) (huv : u ≠ v) (hu : p u = i) (hv : p v = j)
    (B : Finset (Sym2 V)) (hB : DegBounded B d) (load : V → ℕ)
    (q : ℕ) (hq : 0 < q)
    (hbudget : ((∑ x, load x : ℕ) : ℝ) / q + 2 * d < α * (Fintype.card V : ℝ)) :
    ∃ w, G.Adj u w ∧ G.Adj w v ∧ p w = k ∧ load w < q ∧
      s(u, w) ∉ B ∧ s(v, w) ∉ B := by
  let Z := univ.filter (fun v => q ≤ load v)
  have hsat := saturated_card_budget load q
  have hqReal : (0 : ℝ) < q := by exact_mod_cast hq
  have hsatReal : (q : ℝ) * Z.card ≤ (∑ x, load x : ℕ) := by exact_mod_cast hsat
  have hZ : (Z.card : ℝ) ≤ ((∑ x, load x : ℕ) : ℝ) / q :=
    (le_div_iff₀ hqReal).mpr (by simpa only [mul_comm] using hsatReal)
  obtain ⟨w, huw, hwv, hpart, hnZ, heU, heV⟩ :=
    exists_avoiding_of_degree_bound p F G α d hanti i j k hτ u v huv hu hv B Z hB
      (by linarith)
  refine ⟨w, huw, hwv, hpart, ?_, heU, heV⟩
  simpa only [Z, mem_filter, mem_univ, true_and, not_le] using hnZ

end PartitionedTriangleAbsorption.AntiEdgeSelection
