/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups
public import PartitionedTriangleAbsorption.SignedCertificate.Basic
public import Mathlib.Algebra.BigOperators.Fin

/-! # Expanding a signed certificate into occurrences, slots and an edge matching

A certificate term `c_j t_j` contributes `|c_j|` **occurrences** of the actual triangle
`t_j = {r j 0, r j 1, r j 2}`, with the sign of `c_j`; each occurrence has three **slots**,
one per edge (`edgeOf`). For every physical edge `e`,

  `#positive slots on e = [e ∈ P] + #negative slots on e`,

which is exactly the certificate identity at `e`. Gluing fibrewise bijections gives a
bijection `μ : positive slots ≃ P ⊕ negative slots` preserving the physical edge
(`exists_slot_matching`). This is where the integer multiplicities are resolved: an edge
used `m` times positively and `m - [e ∈ P]` times negatively gets `m` distinct positive
slots, each matched to its own partner.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset SignedCertificate

variable {V : Type*} [Fintype V] [DecidableEq V] {ι : Type*} [Fintype ι]

/-- Occurrences of a certificate: term `j` contributes `|c j|` copies. -/
abbrev Occ (c : ι → ℤ) := Σ j : ι, Fin (c j).natAbs

/-- The three edges of `{a, b, c}` in slot order `ab, ac, bc`. -/
def edgeOf (a b c : V) : Fin 3 → Sym2 V := ![s(a, b), s(a, c), s(b, c)]

/-- The physical edge of a slot. -/
def slotBase {c : ι → ℤ} (r : ι → Fin 3 → V) (σ : Occ c × Fin 3) : Sym2 V :=
  edgeOf (r σ.1.1 0) (r σ.1.1 1) (r σ.1.1 2) σ.2

omit [Fintype V] in
theorem card_edgeOf_fiber {a b c : V} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (e : Sym2 V) :
    (univ.filter fun k : Fin 3 => edgeOf a b c k = e).card =
      if e ∈ triEdges ({a, b, c} : Finset V) then 1 else 0 := by
  rw [triEdges_three hab hac hbc, card_filter, Fin.sum_univ_three]
  simp only [edgeOf, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, mem_insert, mem_singleton]
  have n1 := hab.symm; have n2 := hac.symm; have n3 := hbc.symm
  by_cases e1 : s(a, b) = e
  · subst e1; simp [hab, hac, hbc, n1, n2, n3]
  · by_cases e2 : s(a, c) = e
    · subst e2; simp [hab, hac, hbc, n1, n2, n3]
    · by_cases e3 : s(b, c) = e
      · subst e3; simp [hab, hac, hbc, n1, n2, n3]
      · simp [e1, e2, e3, Ne.symm e1, Ne.symm e2, Ne.symm e3]

omit [Fintype V] in
/-- Number of slots of a given sign on a physical edge. -/
theorem card_slots_on_edge {c : ι → ℤ} {t : ι → Finset V} (r : ι → Fin 3 → V)
    (hr : ∀ j, r j 0 ≠ r j 1 ∧ r j 0 ≠ r j 2 ∧ r j 1 ≠ r j 2 ∧
      t j = {r j 0, r j 1, r j 2})
    (sgn : ι → Prop) [DecidablePred sgn] (e : Sym2 V) :
    ((univ.filter fun σ : Occ c × Fin 3 => sgn σ.1.1 ∧ slotBase r σ = e).card : ℤ) =
      ∑ j, (if sgn j then ((c j).natAbs : ℤ) else 0) * ind (triEdges (t j)) e := by
  rw [card_filter]
  push_cast
  rw [Fintype.sum_prod_type, Fintype.sum_sigma]
  refine sum_congr rfl fun j _ => ?_
  obtain ⟨h01, h02, h12, ht⟩ := hr j
  have hfib := card_edgeOf_fiber h01 h02 h12 e
  rw [card_filter] at hfib
  have hinner : ∀ x : Fin (c j).natAbs,
      (∑ k : Fin 3, if sgn j ∧ slotBase r (⟨j, x⟩, k) = e then (1 : ℤ) else 0) =
        if sgn j then ind (triEdges (t j)) e else 0 := by
    intro x
    by_cases hs : sgn j
    · simp only [hs, true_and, ite_true, slotBase]
      have := congrArg (fun m : ℕ => (m : ℤ)) hfib
      push_cast at this
      rw [this, ind, ht]
    · simp [hs]
  rw [Finset.sum_congr rfl fun x _ => hinner x, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  split_ifs <;> simp

omit [Fintype V] in
/-- **Edge-preserving slot matching** from the certificate identity. -/
theorem exists_slot_matching (p : V → Fin 2) (G : SimpleGraph V) {P : Finset (Sym2 V)}
    {t : ι → Finset V} {c : ι → ℤ} (hcert : IsSignedCert p G P t c) (r : ι → Fin 3 → V)
    (hr : ∀ j, r j 0 ≠ r j 1 ∧ r j 0 ≠ r j 2 ∧ r j 1 ≠ r j 2 ∧
      t j = {r j 0, r j 1, r j 2}) :
    ∃ μ : {σ : Occ c × Fin 3 // 0 < c σ.1.1} ≃
        {f // f ∈ P} ⊕ {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1},
      ∀ σ, Sum.elim (fun f => f.1) (fun τ => slotBase r τ.1) (μ σ) = slotBase r σ.1 := by
  classical
  have hfib : ∀ e : Sym2 V,
      Fintype.card {σ : {σ : Occ c × Fin 3 // 0 < c σ.1.1} // slotBase r σ.1 = e} =
        Fintype.card {x : {f // f ∈ P} ⊕ {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} //
          Sum.elim (fun f => f.1) (fun τ => slotBase r τ.1) x = e} := by
    intro e
    rw [Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
        (fun σ : Occ c × Fin 3 => 0 < c σ.1.1) (fun σ => slotBase r σ = e)),
      Fintype.card_congr Equiv.subtypeSum, Fintype.card_sum]
    simp only [Sum.elim_inl, Sum.elim_inr]
    have hnegCard := Fintype.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun σ : Occ c × Fin 3 => ¬ 0 < c σ.1.1) (fun σ => slotBase r σ = e))
    change Fintype.card {σ : Occ c × Fin 3 // 0 < c σ.1.1 ∧ slotBase r σ = e} =
      Fintype.card {f : {f // f ∈ P} // f.1 = e} +
        Fintype.card {τ : {τ : Occ c × Fin 3 // ¬ 0 < c τ.1.1} // slotBase r τ.1 = e}
    rw [hnegCard]
    have hP : Fintype.card {f : {f // f ∈ P} // f.1 = e} = if e ∈ P then 1 else 0 := by
      split_ifs with he
      · rw [Fintype.card_eq_one_iff]
        exact ⟨⟨⟨e, he⟩, rfl⟩, fun x => Subtype.ext (Subtype.ext x.2)⟩
      · rw [Fintype.card_eq_zero_iff]
        exact ⟨fun x => he (x.2 ▸ x.1.2)⟩
    rw [hP, Fintype.card_subtype, Fintype.card_subtype]
    have hpos := card_slots_on_edge (c := c) r hr (fun j => 0 < c j) e
    have hneg := card_slots_on_edge (c := c) r hr (fun j => ¬ 0 < c j) e
    have hc := hcert.2 e
    have key : ∀ j, (if 0 < c j then ((c j).natAbs : ℤ) else 0) * ind (triEdges (t j)) e =
        c j * ind (triEdges (t j)) e +
          (if ¬ 0 < c j then ((c j).natAbs : ℤ) else 0) * ind (triEdges (t j)) e := by
      intro j
      by_cases hj : 0 < c j
      · simp [hj, abs_of_pos hj]
      · simp only [hj, ite_false, ite_true, zero_mul, not_false_eq_true]
        rw [Int.natCast_natAbs, abs_of_nonpos (not_lt.mp hj)]; ring
    rw [Finset.sum_congr rfl fun j _ => key j, sum_add_distrib, ← hc, ← hneg] at hpos
    have : ((univ.filter fun σ : Occ c × Fin 3 => 0 < c σ.1.1 ∧ slotBase r σ = e).card : ℤ) =
        ((if e ∈ P then 1 else 0 : ℕ) : ℤ) +
          ((univ.filter fun σ : Occ c × Fin 3 => ¬ 0 < c σ.1.1 ∧ slotBase r σ = e).card : ℤ) := by
      rw [hpos, ind]; split_ifs <;> simp
    exact_mod_cast this
  exact ⟨Equiv.ofFiberEquiv fun e => Fintype.equivOfCardEq (hfib e),
    fun σ => Equiv.ofFiberEquiv_map _ σ⟩

end PartitionedTriangleAbsorption.SignedHinge
