/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ThirdDistributions
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.AdaptiveWindow

/-!
# The four host faces of an octahedron

The three remaining faces retain one original edge each. Their third-vertex
distributions are kept separately, so opposite masses over an unavailable
old edge can be paired before replacing them with a prism.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer

variable {V : Type*} [DecidableEq V]

def vertexIndicator (Q : Finset V) (v : V) : ℝ := if v ∈ Q then 1 else 0

theorem vertexIndicator_nonneg (Q : Finset V) (v : V) : 0 ≤ vertexIndicator Q v := by
  unfold vertexIndicator
  split_ifs <;> norm_num

def octBase (a b c : V) (f : Fin 3 → V) : TriangleChain V := fun Q =>
  triangleBasis {f 0, f 1, f 2} Q - triangleBasis {f 0, f 1, c} Q -
    triangleBasis {f 0, b, f 2} Q - triangleBasis {a, f 1, f 2} Q

variable [Fintype V] {t : ℕ}

omit [Fintype V] in
theorem octBase_supported (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (a b c : V) (f : Fin 3 → V)
    (ht : Link F (p a) (p b) (p c))
    (hf : OctahedronRealization p G a b c (f 0) (f 1) (f 2)) :
    CopySupported p F G (octBase a b c f) := by
  obtain ⟨h0, h1, h2, h3⟩ := hf.host_faces p G F ht
  exact (((triangleBasis_supported p F G h3).sub (triangleBasis_supported p F G h0)).sub
    (triangleBasis_supported p F G h1)).sub (triangleBasis_supported p F G h2)

theorem octBase_boundary (p : V → Fin t) (G : SimpleGraph V)
    (a b c : V) (f : Fin 3 → V)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hf : OctahedronRealization p G a b c (f 0) (f 1) (f 2)) (e : Sym2 V) :
    boundary (triangleBasis {a, b, c}) e =
      boundary (octBase a b c f) e + boundary (triangleBasis {a, b, f 2}) e +
        boundary (triangleBasis {a, f 1, c}) e + boundary (triangleBasis {f 0, b, c}) e := by
  rw [boundary_face hab hac hbc]
  unfold octBase
  simp only [boundary_sub]
  rw [face_three_adj G hf.AB hf.AC hf.BC,
    boundary_face hf.AB.ne hf.cA.symm.ne hf.cB.symm.ne,
    boundary_face hf.bA.symm.ne hf.AC.ne hf.bC.ne,
    boundary_face hf.aB.ne hf.aC.ne hf.BC.ne,
    boundary_face hab hf.aC.ne hf.bC.ne,
    boundary_face hf.aB.ne hac hf.cB.symm.ne,
    boundary_face hf.bA.symm.ne hf.cA.symm.ne hbc]
  unfold faceBoundary
  ring

namespace ChoiceTree

omit [Fintype V] in
theorem mean_zero_old_triangle_bound (T : ChoiceTree V 3) (s : ℝ) (hs : 0 < s)
    (hT : Lower s T) (Q : Finset V) (hQ : Q.card = 3) :
    |mean T (fun f => triangleBasis {f 0, f 1, f 2} Q)| ≤ (3 / s) ^ 3 := by
  let M : SelectionMask 3 := .selected (.selected (.selected .nil))
  have h := mean_window_bound Q T M s 3 hs (by norm_num) hT
    (by exact_mod_cast hQ.le) (fun f => triangleBasis {f 0, f 1, f 2} Q) 1
    (by norm_num) ?_
  · simpa only [M, SelectionMask.count, one_mul] using h
  intro f hf
  by_cases h : Q = ({f 0, f 1, f 2} : Finset V)
  · simp [h, triangleBasis, M, SelectionMask.Accepts]
  · rw [triangleBasis_eq_zero _ _ h, abs_zero]
    split_ifs <;> norm_num

omit [Fintype V] in
theorem mean_one_old_triangle_bound_01 (T : ChoiceTree V 3) (s : ℝ) (hs : 0 < s)
    (hT : Lower s T) (Q : Finset V) (hQ : Q.card = 3) (c : V) :
    |mean T (fun f => triangleBasis {f 0, f 1, c} Q)| ≤
      vertexIndicator Q c * (3 / s) ^ 2 := by
  let M : SelectionMask 3 := .selected (.selected (.any .nil))
  have h := mean_window_bound Q T M s 3 hs (by norm_num) hT
    (by exact_mod_cast hQ.le) (fun f => triangleBasis {f 0, f 1, c} Q)
    (vertexIndicator Q c) (vertexIndicator_nonneg Q c) ?_
  · simpa only [M, SelectionMask.count] using h
  intro f hf
  by_cases h : Q = ({f 0, f 1, c} : Finset V)
  · simp [h, triangleBasis, vertexIndicator, M, SelectionMask.Accepts]
  · rw [triangleBasis_eq_zero _ _ h, abs_zero]
    exact mul_nonneg (vertexIndicator_nonneg Q c) (by split_ifs <;> norm_num)

omit [Fintype V] in
theorem mean_one_old_triangle_bound_02 (T : ChoiceTree V 3) (s : ℝ) (hs : 0 < s)
    (hT : Lower s T) (Q : Finset V) (hQ : Q.card = 3) (b : V) :
    |mean T (fun f => triangleBasis {f 0, b, f 2} Q)| ≤
      vertexIndicator Q b * (3 / s) ^ 2 := by
  let M : SelectionMask 3 := .selected (.any (.selected .nil))
  have h := mean_window_bound Q T M s 3 hs (by norm_num) hT
    (by exact_mod_cast hQ.le) (fun f => triangleBasis {f 0, b, f 2} Q)
    (vertexIndicator Q b) (vertexIndicator_nonneg Q b) ?_
  · simpa only [M, SelectionMask.count] using h
  intro f hf
  by_cases h : Q = ({f 0, b, f 2} : Finset V)
  · simp [h, triangleBasis, vertexIndicator, M, SelectionMask.Accepts]
  · rw [triangleBasis_eq_zero _ _ h, abs_zero]
    exact mul_nonneg (vertexIndicator_nonneg Q b) (by split_ifs <;> norm_num)

omit [Fintype V] in
theorem mean_one_old_triangle_bound_12 (T : ChoiceTree V 3) (s : ℝ) (hs : 0 < s)
    (hT : Lower s T) (Q : Finset V) (hQ : Q.card = 3) (a : V) :
    |mean T (fun f => triangleBasis {a, f 1, f 2} Q)| ≤
      vertexIndicator Q a * (3 / s) ^ 2 := by
  let M : SelectionMask 3 := .any (.selected (.selected .nil))
  have h := mean_window_bound Q T M s 3 hs (by norm_num) hT
    (by exact_mod_cast hQ.le) (fun f => triangleBasis {a, f 1, f 2} Q)
    (vertexIndicator Q a) (vertexIndicator_nonneg Q a) ?_
  · simpa only [M, SelectionMask.count] using h
  intro f hf
  by_cases h : Q = ({a, f 1, f 2} : Finset V)
  · simp [h, triangleBasis, vertexIndicator, M, SelectionMask.Accepts]
  · rw [triangleBasis_eq_zero _ _ h, abs_zero]
    exact mul_nonneg (vertexIndicator_nonneg Q a) (by split_ifs <;> norm_num)

omit [Fintype V] in
theorem mean_octBase_bound (T : ChoiceTree V 3) (s : ℝ) (hs : 0 < s)
    (hT : Lower s T) (a b c : V) (Q : Finset V) (hQ : Q.card = 3) :
    |mean T (fun f => octBase a b c f Q)| ≤ (3 / s) ^ 3 +
      (vertexIndicator Q a + vertexIndicator Q b + vertexIndicator Q c) * (3 / s) ^ 2 := by
  simp only [octBase, mean_sub]
  have h0 := mean_zero_old_triangle_bound T s hs hT Q hQ
  have h1 := mean_one_old_triangle_bound_01 T s hs hT Q hQ c
  have h2 := mean_one_old_triangle_bound_02 T s hs hT Q hQ b
  have h3 := mean_one_old_triangle_bound_12 T s hs hT Q hQ a
  have htriangle (x y z w : ℝ) : |x - y - z - w| ≤ |x| + |y| + |z| + |w| := by
    have hxy := abs_sub x y
    have hxyz := abs_sub (x - y) z
    have hxyzw := abs_sub (x - y - z) w
    linarith
  exact (htriangle _ _ _ _).trans (by nlinarith only [h0, h1, h2, h3])

end ChoiceTree

#print axioms octBase_supported
#print axioms octBase_boundary
#print axioms ChoiceTree.mean_zero_old_triangle_bound
#print axioms ChoiceTree.mean_one_old_triangle_bound_01
#print axioms ChoiceTree.mean_one_old_triangle_bound_02
#print axioms ChoiceTree.mean_one_old_triangle_bound_12
#print axioms ChoiceTree.mean_octBase_bound

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
