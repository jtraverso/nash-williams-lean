/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedLoadNecessity

/-! # Explicit global and vertex constraints for F0--F3

Each of the four application families has a bipartition `g` of its part labels
such that every permitted type has exactly two `g`-crossing edges and one
`g`-internal edge. Hence the functional "crossing count minus twice internal
count" annihilates every type, and the functional "internal degree minus
crossing degree" is a vertex-cone face at every root. Together with
`TypedLoadNecessity` these give necessary conditions for near-unit loads that
depend only on the graph `J` and the precision.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLoadFamilies

open TypedLoadNecessity TypedApplicationLinks

/-- The bipartition functional on ordered edge counts. On an edge it equals
`2` if the edge crosses `g` and `-4` otherwise. -/
def groupPair {t : ℕ} (g : Fin t → Fin 2) : Fin t → Fin t → ℤ :=
  fun i j => if g i = g j then -2 else 1

/-- The absolute value of `groupPair` on single edges, again as a functional. -/
def groupMass {t : ℕ} (g : Fin t → Fin 2) : Fin t → Fin t → ℤ :=
  fun i j => if g i = g j then 2 else 1

/-- The vertex functional: internal minus crossing degree. -/
def groupFace {t : ℕ} (g : Fin t → Fin 2) (a : Fin t) : Fin t → ℤ :=
  fun i => if g i = g a then 1 else -1

def g0 : Fin 2 → Fin 2 := ![0, 1]
def g4 : Fin 4 → Fin 2 := ![0, 0, 1, 1]

theorem annihilates_F0 : Annihilates F0 (groupPair g0) := by
  unfold Annihilates pairFun groupPair typeEdgeVec
  decide

theorem annihilates_F1 : Annihilates F1 (groupPair g4) := by
  unfold Annihilates pairFun groupPair typeEdgeVec
  decide

theorem annihilates_F2 : Annihilates F2 (groupPair g4) := by
  unfold Annihilates pairFun groupPair typeEdgeVec
  decide

theorem annihilates_F3 : Annihilates F3 (groupPair g4) := by
  unfold Annihilates pairFun groupPair typeEdgeVec
  decide

theorem coneFace_F0 (a : Fin 2) : ConeFace F0 a (groupFace g0 a) := by
  revert a
  unfold ConeFace degFun groupFace typeDegVec
  decide

theorem coneFace_F1 (a : Fin 4) : ConeFace F1 a (groupFace g4 a) := by
  revert a
  unfold ConeFace degFun groupFace typeDegVec
  decide

theorem coneFace_F2 (a : Fin 4) : ConeFace F2 a (groupFace g4 a) := by
  revert a
  unfold ConeFace degFun groupFace typeDegVec
  decide

theorem coneFace_F3 (a : Fin 4) : ConeFace F3 a (groupFace g4 a) := by
  revert a
  unfold ConeFace degFun groupFace typeDegVec
  decide

/-- Ordered edge vectors are symmetric. -/
theorem edgeVec_symm {V : Type*} {t : ℕ} (p : V → Fin t) (E : Finset (Sym2 V)) (i j : Fin t) :
    edgeVec p E i j = edgeVec p E j i := by
  simp only [edgeVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b =>
    simp only [pairVec, Sym2.lift_mk]
    rw [add_comm]
    congr 1 <;> exact if_congr and_comm rfl rfl

/-- **For F0 the balance functional is the only global constraint.** Every
functional annihilating both F0 types agrees on edge vectors with a multiple of
`groupPair g0`. -/
theorem F0_annihilator_unique {V : Type*} (l : Fin 2 → Fin 2 → ℤ) (hl : Annihilates F0 l)
    (p : V → Fin 2) (E : Finset (Sym2 V)) :
    2 * pairFun l (edgeVec p E) = (l 0 1 + l 1 0) * pairFun (groupPair g0) (edgeVec p E) := by
  have e1 : pairFun l (typeEdgeVec {0, 0, 1}) = 2 * l 0 0 + 2 * l 0 1 + 2 * l 1 0 := by
    simp only [pairFun, typeEdgeVec, Fin.isValue, Multiset.insert_eq_cons, Fin.sum_univ_two,
      Multiset.count_cons_self, Multiset.nodup_cons, Multiset.mem_singleton, zero_ne_one,
      not_false_eq_true, Multiset.nodup_singleton, and_self, Multiset.mem_cons, or_false,
      Multiset.count_eq_one_of_mem, Nat.reduceAdd, Nat.cast_ofNat, ne_eq, one_ne_zero,
      Multiset.count_cons_of_ne, or_true, Nat.cast_one, mul_one, Int.reduceMul, ↓reduceIte,
      Int.reduceSub, sub_zero, one_mul, sub_self, mul_zero, add_zero]
    ring
  have e2 : pairFun l (typeEdgeVec {0, 1, 1}) = 2 * l 0 1 + 2 * l 1 0 + 2 * l 1 1 := by
    simp only [pairFun, typeEdgeVec, Fin.isValue, Multiset.insert_eq_cons, Fin.sum_univ_two,
      Multiset.count_cons_self, Multiset.mem_cons, zero_ne_one, Multiset.mem_singleton, or_self,
      not_false_eq_true, Multiset.count_eq_zero_of_notMem, zero_add, Nat.cast_one, mul_one,
      ne_eq, one_ne_zero, Multiset.count_cons_of_ne, Multiset.nodup_singleton,
      Multiset.count_eq_one_of_mem, Nat.reduceAdd, Nat.cast_ofNat, ↓reduceIte, sub_self,
      mul_zero, one_mul, sub_zero, Int.reduceMul, Int.reduceSub]
    ring
  have eg : ∀ M : Fin 2 → Fin 2 → ℤ,
      pairFun (groupPair g0) M = -2 * M 0 0 + M 0 1 + M 1 0 - 2 * M 1 1 := by
    intro M
    simp only [pairFun, groupPair, g0, Fin.isValue, Int.reduceNeg, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, ite_mul, neg_mul,
      one_mul, ↓reduceIte, zero_ne_one, one_ne_zero]
    ring
  have el : ∀ M : Fin 2 → Fin 2 → ℤ,
      pairFun l M = l 0 0 * M 0 0 + l 0 1 * M 0 1 + l 1 0 * M 1 0 + l 1 1 * M 1 1 := by
    intro M
    simp only [pairFun, Fin.sum_univ_two]
    ring
  have h1 := hl {0, 0, 1} (by decide)
  have h2 := hl {0, 1, 1} (by decide)
  rw [e1] at h1
  rw [e2] at h2
  have hs := edgeVec_symm p E 0 1
  rw [el, eg, ← hs]
  linear_combination (edgeVec p E 0 0) * h1 + (edgeVec p E 1 1) * h2

end PartitionedTriangleAbsorption.TypedLoadFamilies
