/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateMatrix

/-! # Assembly of the physical F0 certificate

The three stages are combined here: an initial collection of source-edge
triangles, the half-row correction on a common internal edge, and the even
column repairs.  All identities are pointwise on `Sym2 V`; every triangle is
a real copy of the supplied host; coefficient cost remains linear.

This module is the algebraic consumer.  Supplying the initial peeling and the
two geometric providers from `HostHyp` is a separate obligation.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks

variable {V A B : Type*} [Fintype V] [DecidableEq V]
  [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- Complete integer matrix repair, keeping actual triangle occurrences. -/
theorem physical_matrix_certificate (p : V → Fin 2) (G : SimpleGraph V)
    (R : A → B → ℤ) (r : A → ℤ) (b b' : B)
    (aV : A → V) (bV : B → V) (b0 : V)
    (hr : ∀ a, (∑ c, R a c) = 2 * r a)
    (hTotal : ∑ a, ∑ c, R a c = 0)
    (hRow : ∀ a, r a ≠ 0 → IsCopy p F0 G {aV a,bV b,bV b'})
    (hColumn : ∀ c, ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ a, rowResidual R r b b' a c *
          (physicalEdgeUnit (aV a) (bV c) e - physicalEdgeUnit (aV a) b0 e)) ∧
      T.cost ≤ 13 * ∑ a, |rowResidual R r b b' a c|) :
    ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) = physicalCrossMatrix R aV bV e) ∧
      T.cost ≤ 27 * matrixCost R := by
  have hr0 := halfRows_sum_zero R r hr hTotal
  obtain ⟨TR, hRV, hRE, hRK⟩ := physical_row_repair p G r aV (bV b) (bV b') hr0 hRow
  obtain ⟨TC, hCV, hCE, hCK⟩ := physical_columns_assemble p G
    (rowResidual R r b b') aV bV b0 (rowResidual_rows_zero R r b b' hr) hColumn
  refine ⟨TR ++ TC, valid_append hRV hCV, ?_, ?_⟩
  · intro e
    rw [eval_append, hRE, hCE, ← physicalCrossMatrix_rowCorrection]
    change physicalCrossMatrix (rowCorrection r b b') aV bV e +
      physicalCrossMatrix (fun a c => R a c - rowCorrection r b b' a c) aV bV e = _
    rw [physicalCrossMatrix_sub]
    ring
  · have hNorm := rowResidual_cost R r b b' hr
    have hRows := halfRows_cost R r hr
    have hNonneg : 0 ≤ ∑ a, |r a| := Finset.sum_nonneg fun a _ => abs_nonneg (r a)
    rw [cost_append, hRK]
    nlinarith

/-- The public coefficient bound used by the terminal absorber consumer.  The
loose constant 126 includes all three stages; no host-size factor appears. -/
theorem signed_certificate_from_peeling (p : V → Fin 2) (G : SimpleGraph V)
    (P : Finset (Sym2 V)) (L : IntegralChain (Finset V))
    (R : A → B → ℤ) (r : A → ℤ) (b b' : B)
    (aV : A → V) (bV : B → V) (b0 : V)
    (hL : Valid (IsCopy p F0 G) L)
    (hPeel : ∀ e, ind P e = L.eval (fun t => ind (triEdges t) e) +
      physicalCrossMatrix R aV bV e)
    (hLCost : L.cost ≤ P.card)
    (hRCost : matrixCost R ≤ 4 * P.card)
    (hr : ∀ a, (∑ c, R a c) = 2 * r a)
    (hTotal : ∑ a, ∑ c, R a c = 0)
    (hRow : ∀ a, r a ≠ 0 → IsCopy p F0 G {aV a,bV b,bV b'})
    (hColumn : ∀ c, ∃ T : IntegralChain (Finset V), Valid (IsCopy p F0 G) T ∧
      (∀ e, T.eval (fun t => ind (triEdges t) e) =
        ∑ a, rowResidual R r b b' a c *
          (physicalEdgeUnit (aV a) (bV c) e - physicalEdgeUnit (aV a) b0 e)) ∧
      T.cost ≤ 13 * ∑ a, |rowResidual R r b b' a c|) :
    ∃ n : ℕ, ∃ t : Fin n → Finset V, ∃ c : Fin n → ℤ,
      IsSignedCert p G P t c ∧ certWeight c ≤ 126 * P.card := by
  obtain ⟨T, hTV, hTE, hTK⟩ := physical_matrix_certificate p G R r b b' aV bV b0
    hr hTotal hRow hColumn
  have hIdentity : ∀ e, (L ++ T).eval (fun t => ind (triEdges t) e) = ind P e := by
    intro e
    rw [eval_append, hTE, hPeel]
  obtain ⟨n, t, c, hCert, hCost⟩ := signedCert_of_chain p G P (L ++ T)
    (valid_append hL hTV) hIdentity
  refine ⟨n, t, c, hCert, ?_⟩
  rw [hCost, cost_append]
  have hCard : (0 : ℤ) ≤ P.card := Int.natCast_nonneg _
  nlinarith

#print axioms physical_matrix_certificate
#print axioms signed_certificate_from_peeling

end PartitionedTriangleAbsorption.BlowupB.F0Direct
