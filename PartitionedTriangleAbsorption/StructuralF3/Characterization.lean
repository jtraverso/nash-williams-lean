/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedPieceConditions
public import PartitionedTriangleAbsorption.TypedRefinerCharge
public import PartitionedTriangleAbsorption.TypedLoadCounterexample
public import PartitionedTriangleAbsorption.ClassCertificate.Producer
public import PartitionedTriangleAbsorption.OnePartDivisibility

/-! # Structural F3 divisibility in the four-class setting

Let `cls : V → Fin 4` and let `E` be an edge set none of whose edges lies inside one
class. Then the unchanged predicate `IsIntDiv cls F3 E` is equivalent to

* every vertex has even degree in `E`, and
* the two F3 charges vanish: `charge chi3a cls E = 0` and `charge chi3b cls E = 0`.

In unordered counts `m_ij` these charges are `2(m₀₁ + m₂₃ - m₀₂ - m₁₃)` and
`2(m₀₁ + m₂₃ - m₀₃ - m₁₂)`: the three perfect matchings `{01,23}`, `{02,13}`, `{03,12}` of
the class quadruple carry equally many edges.

Further facts used by the structural refiner:

* `four_dvd_chi3a`, `four_dvd_chi3b`: an even cross-class edge set has both charges divisible
  by `4` (class parities);
* `even3_of_isIntDiv_F3`: structural F3 divisibility implies ordinary (one-part) divisibility,
  so an ordinary refiner may be applied to every eligible structural residue.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3

open Finset TypedApplicationLinks TypedRefinerCharge AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- No edge lies inside one class. -/
def CrossClass (cls : V → Fin 4) (E : Finset (Sym2 V)) : Prop :=
  ∀ a b, s(a, b) ∈ E → cls a ≠ cls b

omit [DecidableEq V] in
theorem CrossClass.loopless {cls : V → Fin 4} {E : Finset (Sym2 V)} (h : CrossClass cls E) :
    ∀ e ∈ E, ¬ e.IsDiag := by
  intro e he
  induction e using Sym2.ind with
  | _ a b =>
    intro hd
    have hab : a = b := by simpa using hd
    subst hab
    exact h a a he rfl

omit [DecidableEq V] in
theorem CrossClass.mono {cls : V → Fin 4} {E E' : Finset (Sym2 V)} (h : CrossClass cls E')
    (hsub : E ⊆ E') : CrossClass cls E := fun a b hab => h a b (hsub hab)

theorem CrossClass.union {cls : V → Fin 4} {E E' : Finset (Sym2 V)} (h : CrossClass cls E)
    (h' : CrossClass cls E') : CrossClass cls (E ∪ E') := by
  intro a b hab
  rcases mem_union.mp hab with hab | hab
  · exact h a b hab
  · exact h' a b hab

omit [DecidableEq V] in
theorem edgeVec_diag_zero {cls : V → Fin 4} {E : Finset (Sym2 V)} (h : CrossClass cls E)
    (i : Fin 4) : edgeVec cls E i i = 0 := by
  simp only [edgeVec, Finset.sum_apply]
  refine Finset.sum_eq_zero fun e he => ?_
  induction e using Sym2.ind with
  | _ a b =>
    have hab := h a b he
    simp only [pairVec, Sym2.lift_mk]
    by_cases ha : cls a = i
    · have hb : ¬ cls b = i := fun hb => hab (ha.trans hb.symm)
      simp [ha, hb]
    · simp [ha]

/-- The sum of the class-`i` row of the edge vector is the degree sum over class `i`. -/
theorem row_sum_even [Finite V] {cls : V → Fin 4} {E : Finset (Sym2 V)} (h : CrossClass cls E)
    (heven : ∀ v, Even (incidentLoad E v)) (i : Fin 4) :
    Even (∑ j, edgeVec cls E i j) := by
  have := Fintype.ofFinite V
  have hrow : ∑ j, edgeVec cls E i j =
      ∑ v ∈ univ.filter (fun v => cls v = i), (incidentLoad E v : ℤ) := by
    simp only [TypedLoadCounterexample.edgeVec_eq_sum_degVec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    exact TypedDivisibilityCollapse.sum_degVec cls E h.loopless v
  rw [hrow]
  exact Finset.even_sum _ fun v _ => (Int.even_coe_nat _).mpr (heven v)

omit [DecidableEq V] in
/-- The first F3 charge in unordered counts. -/
theorem charge_chi3a_eq (cls : V → Fin 4) (E : Finset (Sym2 V)) :
    charge chi3a cls E = 2 * (edgeVec cls E 0 1 + edgeVec cls E 2 3 - edgeVec cls E 0 2 -
      edgeVec cls E 1 3) := by
  have s := TypedLoadFamilies.edgeVec_symm cls E
  simp only [charge, pair, Fin.sum_univ_four, chi3a]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num
  rw [s 1 0, s 2 0, s 3 1, s 3 2]
  ring_nf

omit [DecidableEq V] in
/-- The second F3 charge in unordered counts. -/
theorem charge_chi3b_eq (cls : V → Fin 4) (E : Finset (Sym2 V)) :
    charge chi3b cls E = 2 * (edgeVec cls E 0 1 + edgeVec cls E 2 3 - edgeVec cls E 0 3 -
      edgeVec cls E 1 2) := by
  have s := TypedLoadFamilies.edgeVec_symm cls E
  simp only [charge, pair, Fin.sum_univ_four, chi3b]
  simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  norm_num
  rw [s 1 0, s 3 0, s 2 1, s 3 2]
  ring_nf

/-- Row sums written out with the diagonal removed. -/
theorem rows_even [Finite V] {cls : V → Fin 4} {E : Finset (Sym2 V)} (h : CrossClass cls E)
    (heven : ∀ v, Even (incidentLoad E v)) :
    Even (edgeVec cls E 0 1 + edgeVec cls E 0 2 + edgeVec cls E 0 3) ∧
    Even (edgeVec cls E 0 2 + edgeVec cls E 1 2 + edgeVec cls E 2 3) ∧
    Even (edgeVec cls E 0 3 + edgeVec cls E 1 3 + edgeVec cls E 2 3) := by
  have s := TypedLoadFamilies.edgeVec_symm cls E
  have d := edgeVec_diag_zero h
  have r0 := row_sum_even h heven 0
  have r2 := row_sum_even h heven 2
  have r3 := row_sum_even h heven 3
  simp only [Fin.sum_univ_four, Fin.isValue] at r0 r2 r3
  rw [d 0] at r0
  rw [d 2, s 2 0, s 2 1] at r2
  rw [d 3, s 3 0, s 3 1, s 3 2] at r3
  refine ⟨by simpa using r0, by simpa [add_assoc] using r2, ?_⟩
  simpa [add_assoc] using r3

/-- **Charge divisibility, first charge.** -/
theorem four_dvd_chi3a [Finite V] {cls : V → Fin 4} {E : Finset (Sym2 V)}
    (h : CrossClass cls E) (heven : ∀ v, Even (incidentLoad E v)) :
    (4 : ℤ) ∣ charge chi3a cls E := by
  obtain ⟨⟨k0, hk0⟩, -, ⟨k3, hk3⟩⟩ := rows_even h heven
  rw [charge_chi3a_eq]
  exact ⟨k0 + k3 - edgeVec cls E 0 3 - edgeVec cls E 0 2 - edgeVec cls E 1 3, by linarith⟩

/-- **Charge divisibility, second charge.** -/
theorem four_dvd_chi3b [Finite V] {cls : V → Fin 4} {E : Finset (Sym2 V)}
    (h : CrossClass cls E) (heven : ∀ v, Even (incidentLoad E v)) :
    (4 : ℤ) ∣ charge chi3b cls E := by
  obtain ⟨⟨k0, hk0⟩, ⟨k2, hk2⟩, -⟩ := rows_even h heven
  rw [charge_chi3b_eq]
  exact ⟨k0 + k2 - edgeVec cls E 0 2 - edgeVec cls E 0 3 - edgeVec cls E 1 2, by linarith⟩

omit [DecidableEq V] in
theorem activeEdges_of_crossClass {cls : V → Fin 4} {E : Finset (Sym2 V)}
    (h : CrossClass cls E) : TypedDivisibilityCollapse.ActiveEdges F3 cls E := by
  intro a b hab
  have hne := h a b hab
  obtain ⟨h1, h2⟩ := ClassCertificate.third_ne (cls a) (cls b) hne
  exact ⟨ClassCertificate.third (cls a) (cls b),
    ClassCertificate.distinct_mem_F3 _ _ _ hne (Ne.symm h1) (Ne.symm h2)⟩

/-- **Structural F3 divisibility, exact characterization.** -/
theorem isIntDiv_F3_iff [Finite V] {cls : V → Fin 4} {E : Finset (Sym2 V)}
    (h : CrossClass cls E) :
    IsIntDiv cls F3 E ↔ (∀ v, Even (incidentLoad E v)) ∧ charge chi3a cls E = 0 ∧
      charge chi3b cls E = 0 := by
  constructor
  · intro hd
    exact ⟨TypedDivisibilityCollapse.even_of_isIntDiv TypedTransportExamples.F3_card
      h.loopless hd, charge_eq_zero_of_isIntDiv kills_chi3a hd,
      charge_eq_zero_of_isIntDiv kills_chi3b hd⟩
  · rintro ⟨heven, ha, hb⟩
    refine (TypedPieceConditions.F3_isIntDiv_iff h.loopless).mpr
      ⟨activeEdges_of_crossClass h, heven, ?_⟩
    obtain ⟨⟨k, hk⟩, -, -⟩ := rows_even h heven
    rw [charge_chi3a_eq] at ha
    rw [charge_chi3b_eq] at hb
    have s := TypedLoadFamilies.edgeVec_symm cls E
    have d := edgeVec_diag_zero h
    let c : Multiset (Fin 4) → ℤ := fun τ =>
      if τ = {0, 1, 2} then k - edgeVec cls E 0 3 else
        if τ = {0, 1, 3} then k - edgeVec cls E 0 2 else
        if τ = {0, 2, 3} then k - edgeVec cls E 0 1 else
          edgeVec cls E 1 2 - k + edgeVec cls E 0 3
    refine ⟨c, ?_⟩
    obtain ⟨e01, e02, e03, e12, e13, e23⟩ := ClassCertificate.F3_edge_lattice_eval c
    have n1 : ({0, 1, 3} : Multiset (Fin 4)) ≠ {0, 1, 2} := by decide
    have n2 : ({0, 2, 3} : Multiset (Fin 4)) ≠ {0, 1, 2} := by decide
    have n3 : ({0, 2, 3} : Multiset (Fin 4)) ≠ {0, 1, 3} := by decide
    have n4 : ({1, 2, 3} : Multiset (Fin 4)) ≠ {0, 1, 2} := by decide
    have n5 : ({1, 2, 3} : Multiset (Fin 4)) ≠ {0, 1, 3} := by decide
    have n6 : ({1, 2, 3} : Multiset (Fin 4)) ≠ {0, 2, 3} := by decide
    have c012 : c {0, 1, 2} = k - edgeVec cls E 0 3 := by simp only [c, ite_true]
    have c013 : c {0, 1, 3} = k - edgeVec cls E 0 2 := by
      simp only [c, n1, ite_true, ite_false]
    have c023 : c {0, 2, 3} = k - edgeVec cls E 0 1 := by
      simp only [c, n2, n3, ite_true, ite_false]
    have c123 : c {1, 2, 3} = edgeVec cls E 1 2 - k + edgeVec cls E 0 3 := by
      simp only [c, n4, n5, n6, ite_false]
    have hdiag : ∀ i : Fin 4, (∑ τ ∈ F3, c τ • typeEdgeVec τ) i i = 0 := by
      intro i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun τ hτ => ?_
      have : ∀ τ ∈ F3, ∀ i : Fin 4, typeEdgeVec τ i i = 0 := by
        unfold F3 typeEdgeVec; decide
      rw [this τ hτ i, mul_zero]
    have hsym : ∀ i j : Fin 4, (∑ τ ∈ F3, c τ • typeEdgeVec τ) i j =
        (∑ τ ∈ F3, c τ • typeEdgeVec τ) j i := by
      intro i j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun τ _ => ?_
      simp only [typeEdgeVec, eq_comm (a := i)]
      split_ifs with hij
      · subst hij; ring
      · ring
    funext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk]
    · rw [d 0, hdiag 0]
    · rw [e01, c012, c013]; linarith
    · rw [e02, c012, c023]; linarith
    · rw [e03, c013, c023]; linarith
    · rw [s 1 0, hsym 1 0, e01, c012, c013]; linarith
    · rw [d 1, hdiag 1]
    · rw [e12, c012, c123]; linarith
    · rw [e13, c013, c123]; linarith
    · rw [s 2 0, hsym 2 0, e02, c012, c023]; linarith
    · rw [s 2 1, hsym 2 1, e12, c012, c123]; linarith
    · rw [d 2, hdiag 2]
    · rw [e23, c023, c123]; linarith
    · rw [s 3 0, hsym 3 0, e03, c013, c023]; linarith
    · rw [s 3 1, hsym 3 1, e13, c013, c123]; linarith
    · rw [s 3 2, hsym 3 2, e23, c023, c123]; linarith
    · rw [d 3, hdiag 3]

/-- **Structural F3 divisibility implies ordinary divisibility.** -/
theorem even3_of_isIntDiv_F3 {cls : V → Fin 4} {E : Finset (Sym2 V)}
    (h : CrossClass cls E) (hd : IsIntDiv cls F3 E) : OnePart.Even3 E := by
  refine ⟨?_, TypedDivisibilityCollapse.even_of_isIntDiv TypedTransportExamples.F3_card
    h.loopless hd⟩
  obtain ⟨a, b, c, d, h01, h02, h03, h12, h13, h23⟩ := ClassCertificate.edgeVec_F3_six hd
  have hsum := ClassCertificate.edgeVec_six_sum cls E h
  simp only [ClassCertificate.six] at hsum
  have : (3 : ℤ) ∣ (E.card : ℤ) := ⟨a + b + c + d, by linarith⟩
  exact_mod_cast this

end PartitionedTriangleAbsorption.StructuralF3
