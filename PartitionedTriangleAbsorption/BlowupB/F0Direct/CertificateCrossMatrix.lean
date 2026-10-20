/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificatePeeling

/-! # Exact encoding of a crossing edge function as a rectangular matrix

Each crossing physical edge has exactly one endpoint in the chosen good part,
so the ordered pair of its endpoints is unique.  The encoding preserves the
coefficient norm, takes vertex degrees to row and column sums, and takes F0
charge to the total matrix sum.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset IntegralChain SignedCertificate TypedApplicationLinks

section FinitePush

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

theorem finite_injective_expand (h : A → E) (hI : Function.Injective h) (f : E → ℤ)
    (hS : ∀ e, f e ≠ 0 → ∃ a, h a = e) (e : E) :
    f e = ∑ a, f (h a) * if e = h a then 1 else 0 := by
  classical
  by_cases he : ∃ a, h a = e
  · obtain ⟨a, rfl⟩ := he
    simp [hI.eq_iff]
  · have hfe : f e = 0 := by by_contra hf; exact he (hS e hf)
    have hne : ∀ a, e ≠ h a := fun a ha => he ⟨a, ha.symm⟩
    simp [hfe, hne]

theorem finite_injective_sum (h : A → E) (hI : Function.Injective h) (f : E → ℤ)
    (hS : ∀ e, f e ≠ 0 → ∃ a, h a = e) (w : E → ℤ) :
    (∑ e, f e * w e) = ∑ a, f (h a) * w (h a) := by
  classical
  calc
    _ = ∑ e, ∑ a, (f (h a) * if e = h a then 1 else 0) * w e := by
      apply Finset.sum_congr rfl
      intro e _
      rw [finite_injective_expand h hI f hS e, Finset.sum_mul]
    _ = ∑ a, ∑ e, (f (h a) * if e = h a then 1 else 0) * w e := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      simp [mul_ite, ite_mul]

end FinitePush

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem otherPart_ne (i : Fin 2) : other0 i ≠ i := by
  revert i
  decide

private theorem eq_or_otherPart (i j : Fin 2) : j = i ∨ j = other0 i := by
  revert i j
  decide

abbrev PartVertex (p : V → Fin 2) (i : Fin 2) := {v : V // p v = i}

def crossEdge (p : V → Fin 2) (i : Fin 2)
    (z : PartVertex p i × PartVertex p (other0 i)) : Sym2 V := s(z.1.val,z.2.val)

theorem partVertex_ne_other (p : V → Fin 2) (i : Fin 2)
    (a : PartVertex p i) (b : PartVertex p (other0 i)) : a.val ≠ b.val := by
  intro h
  exact otherPart_ne i (b.property.symm.trans ((congrArg p h).symm.trans a.property))

theorem crossEdge_injective (p : V → Fin 2) (i : Fin 2) : Function.Injective (crossEdge p i) := by
  intro x y h
  rcases Sym2.eq_iff.mp h with h | h
  · exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)
  · exact False.elim (partVertex_ne_other p i x.1 y.2 h.1)

theorem crossEdge_not_internal (p : V → Fin 2) (i : Fin 2)
    (z : PartVertex p i × PartVertex p (other0 i)) : ¬ IsInternal p (crossEdge p i z) := by
  simp only [IsInternal, crossEdge, Sym2.map_mk, Sym2.mk_isDiag_iff,
    z.1.property, z.2.property]
  exact (otherPart_ne i).symm

theorem crossEdge_surjective_on_crossing (p : V → Fin 2) (i : Fin 2)
    (e : Sym2 V) (h : ¬ IsInternal p e) :
    ∃ z : PartVertex p i × PartVertex p (other0 i), crossEdge p i z = e := by
  induction e using Sym2.ind with
  | _ u v =>
    have huv : p u ≠ p v := by simpa [IsInternal] using h
    rcases eq_or_otherPart i (p u) with hu | hu <;>
      rcases eq_or_otherPart i (p v) with hv | hv
    · exact False.elim (huv (hu.trans hv.symm))
    · exact ⟨(⟨u,hu⟩,⟨v,hv⟩), rfl⟩
    · refine ⟨(⟨v,hv⟩,⟨u,hu⟩), ?_⟩
      exact Sym2.eq_swap
    · exact False.elim (huv (hu.trans hv.symm))

def crossingMatrix (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (a : PartVertex p i) (b : PartVertex p (other0 i)) : ℤ := f s(a.val,b.val)

theorem cross_support (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (hF : ∀ e, IsInternal p e → f e = 0) (e : Sym2 V) (he : f e ≠ 0) :
    ∃ z, crossEdge p i z = e :=
  crossEdge_surjective_on_crossing p i e (fun h => he (hF e h))

theorem crossingMatrix_evaluate (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (hF : ∀ e, IsInternal p e → f e = 0) (e : Sym2 V) :
    physicalCrossMatrix (crossingMatrix p i f) Subtype.val Subtype.val e = f e := by
  have h := finite_injective_expand (crossEdge p i) (crossEdge_injective p i) f
    (cross_support p i f hF) e
  simp only [crossEdge, Fintype.sum_prod_type] at h
  rw [h]
  unfold physicalCrossMatrix
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  unfold crossingMatrix physicalEdgeUnit
  congr 1

theorem crossingMatrix_cost (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (hF : ∀ e, IsInternal p e → f e = 0) :
    matrixCost (crossingMatrix p i f) = edgeFunctionCost f := by
  have hAbs : ∀ e, |f e| ≠ 0 → ∃ z, crossEdge p i z = e := by
    intro e he
    exact cross_support p i f hF e (fun h => he (by rw [h, abs_zero]))
  have h := finite_injective_sum (crossEdge p i) (crossEdge_injective p i)
    (fun e => |f e|) hAbs (fun _ => 1)
  simpa [matrixCost, edgeFunctionCost, crossingMatrix, crossEdge,
    Fintype.sum_prod_type] using h.symm

theorem crossEdge_degree_left (p : V → Fin 2) (i : Fin 2) (a : PartVertex p i)
    (z : PartVertex p i × PartVertex p (other0 i)) :
    (∑ k, degContrib p a.val (crossEdge p i z) k) = if a = z.1 then 1 else 0 := by
  have hn : ¬ (crossEdge p i z).IsDiag := by
    simpa [crossEdge] using partVertex_ne_other p i z.1 z.2
  rw [IntegerCertificate.sum_degContrib a.val hn]
  have hne := partVertex_ne_other p i a z.2
  simp [crossEdge, Sym2.mem_iff, hne, Subtype.ext_iff]

theorem crossEdge_degree_right (p : V → Fin 2) (i : Fin 2)
    (b : PartVertex p (other0 i)) (z : PartVertex p i × PartVertex p (other0 i)) :
    (∑ k, degContrib p b.val (crossEdge p i z) k) = if b = z.2 then 1 else 0 := by
  have hn : ¬ (crossEdge p i z).IsDiag := by
    simpa [crossEdge] using partVertex_ne_other p i z.1 z.2
  rw [IntegerCertificate.sum_degContrib b.val hn]
  have hne := (partVertex_ne_other p i z.1 b).symm
  simp [crossEdge, Sym2.mem_iff, hne, Subtype.ext_iff]

theorem crossingMatrix_rowSum (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (hF : ∀ e, IsInternal p e → f e = 0) (a : PartVertex p i) :
    (∑ b, crossingMatrix p i f a b) = vertexDegree p f a.val := by
  rw [vertexDegree, finite_injective_sum (crossEdge p i) (crossEdge_injective p i) f
    (cross_support p i f hF)]
  simp_rw [crossEdge_degree_left]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp [crossEdge, crossingMatrix, mul_ite]

theorem crossingMatrix_columnSum (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (hF : ∀ e, IsInternal p e → f e = 0) (b : PartVertex p (other0 i)) :
    (∑ a, crossingMatrix p i f a b) = vertexDegree p f b.val := by
  rw [vertexDegree, finite_injective_sum (crossEdge p i) (crossEdge_injective p i) f
    (cross_support p i f hF)]
  simp_rw [crossEdge_degree_right]
  rw [Fintype.sum_prod_type]
  simp [crossEdge, crossingMatrix, mul_ite]

theorem crossEdge_charge (p : V → Fin 2) (i : Fin 2)
    (z : PartVertex p i × PartVertex p (other0 i)) :
    IntegerCertificate.kappa p (crossEdge p i z) = 1 := by
  have h : p z.1.val ≠ p z.2.val := by
    rw [z.1.property, z.2.property]
    exact (otherPart_ne i).symm
  simp [IntegerCertificate.kappa, crossEdge, h]

theorem crossingMatrix_total (p : V → Fin 2) (i : Fin 2) (f : Sym2 V → ℤ)
    (hF : ∀ e, IsInternal p e → f e = 0) :
    (∑ a, ∑ b, crossingMatrix p i f a b) = IntegerCertificate.charge p f := by
  rw [IntegerCertificate.charge,
    finite_injective_sum (crossEdge p i) (crossEdge_injective p i) f (cross_support p i f hF)]
  simp only [crossEdge_charge, mul_one]
  simp [crossingMatrix, crossEdge, Fintype.sum_prod_type]

#print axioms crossingMatrix_evaluate
#print axioms crossingMatrix_rowSum
#print axioms crossingMatrix_columnSum
#print axioms crossingMatrix_total

end PartitionedTriangleAbsorption.BlowupB.F0Direct
