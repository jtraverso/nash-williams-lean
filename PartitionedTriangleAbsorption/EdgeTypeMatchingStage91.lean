/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPreparationStage90
public import Mathlib.Logic.Equiv.Basic

/-! # Matching finite physical edge tokens by their endpoint labels

Equality of ordered type vectors implies a label-type-preserving bijection
between the actual edge sets. This is static token matching, not an incidence
invariant for catalyst surgery and not a terminal triangle decomposition.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.EdgeTypeMatchingStage91

open Finset

variable {V W : Type*} {t : ℕ}

/-- Diagonal types contribute twice; off-diagonal types contribute once. -/
theorem pairVec_indicator (p : V → Fin t) (e : Sym2 V) (i j : Fin t) :
    pairVec p e i j =
      if Sym2.map p e = s(i,j) then (if i = j then 2 else 1) else 0 := by
  induction e using Sym2.ind with
  | h u v =>
    by_cases hij : i = j
    · subst j
      by_cases hu : p u = i <;> by_cases hv : p v = i <;>
        simp [pairVec, hu, hv]
    · by_cases hui : p u = i <;> by_cases huj : p u = j <;>
        by_cases hvi : p v = i <;> by_cases hvj : p v = j <;>
        simp_all [pairVec]

/-- Recover the number of actual edges of a type from its vector coordinate. -/
theorem edgeVec_count (p : V → Fin t) (X : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p X i j = (if i = j then 2 else 1) *
      ((X.filter (fun e => Sym2.map p e = s(i,j))).card : ℤ) := by
  classical
  simp only [edgeVec, sum_apply]
  simp_rw [pairVec_indicator]
  rw [← sum_filter]
  simp [mul_comm]

/-- Equal vectors give equal multiplicities of each unordered label pair. -/
theorem type_count_eq (p : V → Fin t) (q : W → Fin t)
    (X : Finset (Sym2 V)) (Y : Finset (Sym2 W))
    (hvec : edgeVec p X = edgeVec q Y) (i j : Fin t) :
    (X.filter (fun e => Sym2.map p e = s(i,j))).card =
      (Y.filter (fun e => Sym2.map q e = s(i,j))).card := by
  have h := congrFun (congrFun hvec i) j
  rw [edgeVec_count, edgeVec_count] at h
  have hw : (if i = j then (2 : ℤ) else 1) ≠ 0 := by
    split_ifs <;> norm_num
  have hc := mul_left_cancel₀ hw h
  exact_mod_cast hc

/-- The fibre of a finite edge subtype has the cardinality of its filter. -/
theorem fiber_card (p : V → Fin t) (X : Finset (Sym2 V)) (k : Sym2 (Fin t)) :
    Fintype.card {e : X // Sym2.map p e.1 = k} =
      (X.filter (fun e => Sym2.map p e = k)).card := by
  classical
  let f : {e : X // Sym2.map p e.1 = k} ≃
      {e // e ∈ X.filter (fun e => Sym2.map p e = k)} := {
    toFun := fun e => ⟨e.1.1, mem_filter.mpr ⟨e.1.2, e.2⟩⟩
    invFun := fun e => ⟨⟨e.1, (mem_filter.mp e.2).1⟩, (mem_filter.mp e.2).2⟩
    left_inv := by intro e; rfl
    right_inv := by intro e; rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr f

/-- Produce a bijection of the actual edge tokens, preserving unordered labels.
Neither a supplied bijection nor a vertex map is required. -/
theorem exists_edge_equiv (p : V → Fin t) (q : W → Fin t)
    (X : Finset (Sym2 V)) (Y : Finset (Sym2 W))
    (hvec : edgeVec p X = edgeVec q Y) :
    ∃ f : X ≃ Y, ∀ e : X, Sym2.map q (f e).1 = Sym2.map p e.1 := by
  classical
  have hcard (k : Sym2 (Fin t)) :
      Fintype.card {e : X // Sym2.map p e.1 = k} =
        Fintype.card {e : Y // Sym2.map q e.1 = k} := by
    rw [fiber_card, fiber_card]
    induction k using Sym2.ind with
    | h i j => exact type_count_eq p q X Y hvec i j
  let e := fun k => Fintype.equivOfCardEq (hcard k)
  let f : X ≃ Y := Equiv.ofFiberEquiv
    (f := fun x : X => Sym2.map p x.1) (g := fun y : Y => Sym2.map q y.1) e
  refine ⟨f, ?_⟩
  intro x
  exact Equiv.ofFiberEquiv_map
    (f := fun x : X => Sym2.map p x.1) (g := fun y : Y => Sym2.map q y.1) e x

end PartitionedTriangleAbsorption.EdgeTypeMatchingStage91
