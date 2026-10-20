/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.Certificate

/-! # Exact row and column bookkeeping for the F0 certificate

If an integer matrix has even row sums and total sum zero, each half-row sum
can be removed using two fixed columns.  Column sums do not change.  The
residual has zero row sums and at most twice the original coefficient norm.
The zero-row condition is exactly what cancels the common anchor column in
the physical triangle lift.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def matrixCost (R : A → B → ℤ) : ℤ := ∑ a, ∑ b, |R a b|

def rowCorrection (r : A → ℤ) (b b' : B) (a : A) (c : B) : ℤ :=
  r a * (vertexUnit b c + vertexUnit b' c)

def rowResidual (R : A → B → ℤ) (r : A → ℤ) (b b' : B) (a : A) (c : B) : ℤ :=
  R a c - rowCorrection r b b' a c

theorem matrixCost_nonneg (R : A → B → ℤ) : 0 ≤ matrixCost R :=
  Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => abs_nonneg (R a b)

theorem rowCorrection_sum (r : A → ℤ) (b b' : B) (a : A) :
    (∑ c, rowCorrection r b b' a c) = 2 * r a := by
  simp [rowCorrection, Finset.mul_sum, vertexUnit, mul_add, Finset.sum_add_distrib]
  ring

theorem rowCorrection_column (r : A → ℤ) (b b' c : B) :
    (∑ a, rowCorrection r b b' a c) =
      (∑ a, r a) * (vertexUnit b c + vertexUnit b' c) := by
  simp only [rowCorrection, Finset.sum_mul]

theorem rowCorrection_cost (r : A → ℤ) (b b' : B) :
    matrixCost (rowCorrection r b b') = 2 * ∑ a, |r a| := by
  have h : ∀ c : B, 0 ≤ vertexUnit b c + vertexUnit b' c := by
    intro c
    simp only [vertexUnit]
    split_ifs <;> norm_num
  unfold matrixCost
  simp only [rowCorrection, abs_mul, abs_of_nonneg (h _)]
  simp [vertexUnit, mul_add, Finset.sum_add_distrib]
  ring

theorem halfRows (R : A → B → ℤ) (h : ∀ a, Even (∑ b, R a b)) :
    ∃ r : A → ℤ, ∀ a, (∑ b, R a b) = 2 * r a := by
  choose r hr using h
  refine ⟨r, fun a => ?_⟩
  rw [hr a]
  ring

theorem halfRows_sum_zero (R : A → B → ℤ) (r : A → ℤ)
    (hr : ∀ a, (∑ b, R a b) = 2 * r a) (h0 : ∑ a, ∑ b, R a b = 0) :
    ∑ a, r a = 0 := by
  have h := h0
  simp_rw [hr, ← Finset.mul_sum] at h
  omega

theorem halfRows_cost (R : A → B → ℤ) (r : A → ℤ)
    (hr : ∀ a, (∑ b, R a b) = 2 * r a) :
    2 * (∑ a, |r a|) ≤ matrixCost R := by
  have h : ∀ a, 2 * |r a| ≤ ∑ b, |R a b| := by
    intro a
    have h := Finset.abs_sum_le_sum_abs (f := R a) Finset.univ
    rw [hr a, abs_mul] at h
    norm_num at h
    exact h
  simpa only [Finset.mul_sum, matrixCost] using Finset.sum_le_sum (fun a _ => h a)

theorem rowResidual_rows_zero (R : A → B → ℤ) (r : A → ℤ) (b b' : B)
    (hr : ∀ a, (∑ c, R a c) = 2 * r a) :
    ∀ a, (∑ c, rowResidual R r b b' a c) = 0 := by
  intro a
  simp only [rowResidual, Finset.sum_sub_distrib, rowCorrection_sum, hr, sub_self]

theorem rowResidual_columns (R : A → B → ℤ) (r : A → ℤ) (b b' c : B)
    (hr0 : ∑ a, r a = 0) :
    (∑ a, rowResidual R r b b' a c) = ∑ a, R a c := by
  simp only [rowResidual, Finset.sum_sub_distrib, rowCorrection_column, hr0,
    zero_mul, sub_zero]

theorem rowResidual_cost (R : A → B → ℤ) (r : A → ℤ) (b b' : B)
    (hr : ∀ a, (∑ c, R a c) = 2 * r a) :
    matrixCost (rowResidual R r b b') ≤ 2 * matrixCost R := by
  have hSub : matrixCost (rowResidual R r b b') ≤
      matrixCost R + matrixCost (rowCorrection r b b') := by
    unfold matrixCost rowResidual
    simp only [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun c _ =>
      by simpa using abs_sub_le (R a c) 0 (rowCorrection r b b' a c)
  rw [rowCorrection_cost] at hSub
  linarith [halfRows_cost R r hr]

variable {V : Type*} [Fintype V] [DecidableEq V]

def physicalCrossMatrix (R : A → B → ℤ) (aV : A → V) (bV : B → V) (e : Sym2 V) : ℤ :=
  ∑ a, ∑ b, R a b * physicalEdgeUnit (aV a) (bV b) e

theorem physicalCrossMatrix_sub (R S : A → B → ℤ) (aV : A → V) (bV : B → V)
    (e : Sym2 V) :
    physicalCrossMatrix (fun a b => R a b - S a b) aV bV e =
      physicalCrossMatrix R aV bV e - physicalCrossMatrix S aV bV e := by
  simp only [physicalCrossMatrix, sub_mul, Finset.sum_sub_distrib]

theorem physicalCrossMatrix_rowCorrection (r : A → ℤ) (b b' : B)
    (aV : A → V) (bV : B → V) (e : Sym2 V) :
    physicalCrossMatrix (rowCorrection r b b') aV bV e =
      ∑ a, r a * (physicalEdgeUnit (aV a) (bV b) e +
        physicalEdgeUnit (aV a) (bV b') e) := by
  unfold physicalCrossMatrix rowCorrection
  apply Finset.sum_congr rfl
  intro a _
  simp [vertexUnit, mul_add, add_mul, Finset.sum_add_distrib]

/-- One common internal edge removes all half-row sums.  Its coefficient is
zero in aggregate; no auxiliary anchor triangle is required in this step. -/
theorem physical_row_repair (p : V → Fin 2) (G : SimpleGraph V)
    (r : A → ℤ) (aV : A → V) (b b' : V) (hr0 : ∑ a, r a = 0)
    (hT : ∀ a, r a ≠ 0 → IsCopy p F0 G {aV a,b,b'}) :
    ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ a, r a * (physicalEdgeUnit (aV a) b e + physicalEdgeUnit (aV a) b' e)) ∧
      T.cost = ∑ a, |r a| := by
  let T := IntegralChain.sum (fun a => term (r a) ({aV a,b,b'} : Finset V))
  refine ⟨T, valid_sum (fun a => valid_term (hT a)), ?_, ?_⟩
  · intro e
    simp only [T, eval_sum, eval_term]
    have h : ∀ a,
        r a * ind (triEdges ({aV a,b,b'} : Finset V)) e =
          r a * (physicalEdgeUnit (aV a) b e + physicalEdgeUnit (aV a) b' e +
            physicalEdgeUnit b b' e) := by
      intro a
      by_cases ha : r a = 0
      · simp [ha]
      · obtain ⟨ha1, ha2, hbb⟩ := SimpleGraph.is3Clique_triple_iff.mp (hT a ha).1
        rw [ind_triangle ha1.ne ha2.ne hbb.ne]
    simp_rw [h, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hr0]
    simp
  · simp only [T, cost_sum, cost_term]

/-- Assemble all physical column repairs.  The common anchor column cancels
because each row sum is zero, even when the number of columns is unbounded. -/
theorem physical_columns_assemble (p : V → Fin 2) (G : SimpleGraph V)
    (R : A → B → ℤ) (aV : A → V) (bV : B → V) (b0 : V)
    (hR : ∀ a, (∑ b, R a b) = 0)
    (hC : ∀ b, ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ a, R a b * (physicalEdgeUnit (aV a) (bV b) e - physicalEdgeUnit (aV a) b0 e)) ∧
      T.cost ≤ 13 * ∑ a, |R a b|) :
    ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) = physicalCrossMatrix R aV bV e) ∧
      T.cost ≤ 13 * matrixCost R := by
  classical
  choose C hV hE hK using hC
  refine ⟨IntegralChain.sum C, valid_sum hV, ?_, ?_⟩
  · intro e
    simp only [eval_sum, hE]
    rw [Finset.sum_comm]
    unfold physicalCrossMatrix
    apply Finset.sum_congr rfl
    intro a _
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hR,
      zero_mul, sub_zero]
  · rw [cost_sum]
    calc
      _ ≤ ∑ b, 13 * ∑ a, |R a b| := Finset.sum_le_sum fun b _ => hK b
      _ = 13 * matrixCost R := by rw [← Finset.mul_sum, Finset.sum_comm]; rfl

#print axioms rowResidual_cost
#print axioms physical_row_repair
#print axioms physical_columns_assemble

end PartitionedTriangleAbsorption.BlowupB.F0Direct
