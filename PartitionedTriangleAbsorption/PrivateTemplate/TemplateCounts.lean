/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.TemplateDecomp

/-!
# Exact counts for the template

* `|A| = 105 m`;
* `|U| = 34 m + 1` auxiliaries (for `m > 0`);
* `deg_A (root r) = 8 · #{j | xr j = r} = 4 · deg_P (root r)`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart AntiEdgeSelection

variable {Rt : Type*} [DecidableEq Rt] {m : ℕ}

theorem card_auxV (hm : 0 < m) : Fintype.card (AuxV m) = 34 * m + 1 := by
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_tag, mul_comm]
  congr 1
  rw [Fintype.card_subtype]
  simp [hm]

variable {σt : Equiv.Perm (Fin m)} {xr : Fin m → Rt} (h3 : 3 ∣ m)

/-! ### Piece cardinalities -/

theorem card_edgesP1 (hne : ∀ j, xr j ≠ xr (σt j)) : (edgesP1 σt xr).card = 2 * m := by
  rw [edgesP1, card_union_of_disjoint, card_posEdges, card_posEdges, Fintype.card_fin]
  · ring
  · intro j j' h; aesop
  · intro j j' h; aesop
  · rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨j, rfl⟩ := mem_posEdges.mp he
    obtain ⟨j', h⟩ := mem_posEdges.mp he'
    simp only [Sym2.eq_iff, reduceCtorEq, false_and, Sum.inl.injEq, Sum.inr.injEq,
      Prod.mk.injEq, and_true, false_or] at h
    obtain ⟨h1, rfl⟩ := h
    exact hne j h1

theorem card_edgesP2 : (edgesP2 σt xr).card = 4 * m := by
  rw [edgesP2, (transformerData_P σt xr).card_srcEdges, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, mul_comm]

theorem card_edgesTP : (edgesTP σt xr).card = 44 * m := by
  rw [edgesTP, (transformerData_P σt xr).card_transEdges, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  ring

theorem card_edgesJ : (edgesJ σt (Rt := Rt)).card = 4 * m := by
  rw [edgesJ, card_posEdges, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  fin_cases k <;> fin_cases k' <;> simp [petalV] at h ⊢ <;> simp_all

theorem card_edgesTQ : (edgesTQ h3 (Rt := Rt)).card = 44 * m := by
  rw [edgesTQ, (transformerData_Q h3).card_transEdges, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  ring

theorem card_edgesQ2 : (edgesQ2 h3 (Rt := Rt)).card = 4 * m := by
  rw [edgesQ2, (transformerData_Q h3).card_srcEdges, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, mul_comm]

theorem card_edgesQ1 : (edgesQ1 h3 (Rt := Rt)).card = 2 * m := by
  rw [edgesQ1, card_union_of_disjoint, card_posEdges, card_posEdges, Fintype.card_fin]
  · ring
  · intro j j' h; aesop
  · intro j j' h; aesop
  · rw [Finset.disjoint_left]
    intro e he he'
    obtain ⟨j, rfl⟩ := mem_posEdges.mp he
    obtain ⟨j', h⟩ := mem_posEdges.mp he'
    simp only [Sym2.eq_iff, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
    rcases h with ⟨⟨-, h⟩, -⟩ | ⟨⟨h1, -⟩, ⟨rfl, -⟩⟩
    · exact absurd h (by decide)
    · exact triPerm_ne h3 j h1.symm

theorem card_edgesQ : (edgesQ h3 (Rt := Rt)).card = m := by
  rw [edgesQ, card_posEdges (qEdge_injective h3), Fintype.card_fin]

/-- **Edge count.** The template has exactly `105 m` edges. -/
theorem card_template (hne : ∀ j, xr j ≠ xr (σt j)) : (template σt xr h3).card = 105 * m := by
  have i1 := pieceIn_P1 σt xr
  have i2 := pieceIn_P2 σt xr
  have i3 := pieceIn_TP σt xr
  have i4 := pieceIn_J σt (Rt := Rt)
  have i5 := pieceIn_TQ h3 (Rt := Rt)
  have i6 := pieceIn_Q2 h3 (Rt := Rt)
  have i7 := pieceIn_Q1 h3 (Rt := Rt)
  have i8 := pieceIn_Q h3 (Rt := Rt)
  rw [template, card_union_of_disjoint (((((((i1.union i2).union i3).union i4).union i5).union
      i6).union i7).disjoint i8 (by decide)),
    card_union_of_disjoint ((((((i1.union i2).union i3).union i4).union i5).union i6).disjoint
      i7 (by decide)),
    card_union_of_disjoint (((((i1.union i2).union i3).union i4).union i5).disjoint i6
      (by decide)),
    card_union_of_disjoint ((((i1.union i2).union i3).union i4).disjoint i5 (by decide)),
    card_union_of_disjoint (((i1.union i2).union i3).disjoint i4 (by decide)),
    card_union_of_disjoint ((i1.union i2).disjoint i3 (by decide)),
    card_union_of_disjoint (i1.disjoint i2 (by decide)),
    card_edgesP1 hne, card_edgesP2, card_edgesTP, card_edgesJ, card_edgesTQ,
    card_edgesQ2, card_edgesQ1, card_edgesQ]
  ring

/-! ### Root degrees -/

theorem incidentLoad_root_eq_zero {X : Finset (Sym2 (TV Rt m))} (hX : ∀ e ∈ X, (kappa e).1 ≠ 0)
    (r : Rt) : incidentLoad X (Sum.inl r) = 0 := by
  unfold incidentLoad
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hr
  exact hX e he (kappa_fst_of_root r hr)

theorem card_xP_root (r : Rt) :
    (univ.filter fun i => xP xr i = (Sum.inl r : TV Rt m)).card =
      (univ.filter fun j => xr j = r).card := by
  symm
  apply card_bij (fun j _ => (j, (0 : Fin 4)))
  · intro j hj
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simpa only [xP, pathV, Matrix.cons_val_zero, Sum.inl.injEq] using (mem_filter.mp hj).2
  · intro j _ j' _ h; simpa using h
  · rintro ⟨j, k⟩ hk
    simp only [mem_filter, mem_univ, true_and] at hk
    fin_cases k <;> dsimp [xP, pathV] at hk
    · exact ⟨j, mem_filter.mpr ⟨mem_univ _, Sum.inl.inj hk⟩, rfl⟩
    · cases hk
    · cases hk
    · cases hk

/-- Degree of a root in the lifted piece. -/
theorem incidentLoad_edgesP_root (hne : ∀ j, xr j ≠ xr (σt j))
    (hinj : Function.Injective fun j => s(xr j, xr (σt j))) (r : Rt) :
    incidentLoad (edgesP σt xr) (Sum.inl r) = 2 * (univ.filter fun j => xr j = r).card := by
  rw [edgesP, incidentLoad_posEdges]
  · simp only [Sum.inl.injEq]
    rw [card_filter_perm σt xr r]
    ring
  · intro j j' h; apply hinj; simpa using h
  · intro j; simpa using hne j

/-- **Root degree.** A root meets `8 · #{j | xr j = r}` template edges. -/
theorem incidentLoad_template_root (hne : ∀ j, xr j ≠ xr (σt j)) (r : Rt) :
    incidentLoad (template σt xr h3) (Sum.inl r) = 8 * (univ.filter fun j => xr j = r).card := by
  have i1 := pieceIn_P1 σt xr
  have i2 := pieceIn_P2 σt xr
  have i3 := pieceIn_TP σt xr
  have i4 := pieceIn_J σt (Rt := Rt)
  have i5 := pieceIn_TQ h3 (Rt := Rt)
  have i6 := pieceIn_Q2 h3 (Rt := Rt)
  have i7 := pieceIn_Q1 h3 (Rt := Rt)
  have i8 := pieceIn_Q h3 (Rt := Rt)
  rw [template, incidentLoad_union (((((((i1.union i2).union i3).union i4).union i5).union
      i6).union i7).disjoint i8 (by decide)),
    incidentLoad_union ((((((i1.union i2).union i3).union i4).union i5).union i6).disjoint
      i7 (by decide)),
    incidentLoad_union (((((i1.union i2).union i3).union i4).union i5).disjoint i6
      (by decide)),
    incidentLoad_union ((((i1.union i2).union i3).union i4).disjoint i5 (by decide)),
    incidentLoad_union (((i1.union i2).union i3).disjoint i4 (by decide)),
    incidentLoad_union ((i1.union i2).disjoint i3 (by decide)),
    incidentLoad_union (i1.disjoint i2 (by decide))]
  rw [incidentLoad_root_eq_zero (X := edgesJ σt) (fun e he => by simp [kappa_J σt e he]),
    incidentLoad_root_eq_zero (X := edgesTQ h3) (kappa_TQ_fst h3),
    incidentLoad_root_eq_zero (X := edgesQ2 h3)
      (fun e he => by rcases kappa_Q2 h3 e he with h | h <;> simp [h]),
    incidentLoad_root_eq_zero (X := edgesQ1 h3) (fun e he => by simp [kappa_Q1 h3 e he]),
    incidentLoad_root_eq_zero (X := edgesQ h3) (fun e he => by simp [kappa_Q h3 e he])]
  -- `P₁`
  have hP1 : incidentLoad (edgesP1 σt xr) (Sum.inl r) =
      2 * (univ.filter fun j => xr j = r).card := by
    have hd : Disjoint (posEdges (fun j => (Sum.inl (xr j) : TV Rt m)) fun j => aux j .p1)
        (posEdges (fun j => aux j .p1) fun j => Sum.inl (xr (σt j))) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨j, rfl⟩ := mem_posEdges.mp he
      obtain ⟨j', h⟩ := mem_posEdges.mp he'
      simp only [Sym2.eq_iff, reduceCtorEq, false_and, Sum.inl.injEq, Sum.inr.injEq,
        Prod.mk.injEq, and_true, false_or] at h
      obtain ⟨h1, rfl⟩ := h
      exact hne j h1
    rw [edgesP1, incidentLoad_union hd, incidentLoad_posEdges, incidentLoad_posEdges]
    · simp only [Sum.inl.injEq, reduceCtorEq, filter_false, card_empty, add_zero, zero_add]
      rw [card_filter_perm σt xr r]
      ring
    · intro j j' h; aesop
    · intro j; simp
    · intro j j' h; aesop
    · intro j; simp
  -- `P₂`
  have hP2 : incidentLoad (edgesP2 σt xr) (Sum.inl r) =
      2 * (univ.filter fun j => xr j = r).card := by
    have hT := transformerData_P σt xr
    rw [edgesP2, srcEdges, incidentLoad_posEdges hT.hxinj hT.hx,
      card_filter_perm (blowPerm σt) (xP xr), card_xP_root]
    ring
  -- `T_P`
  have hTP : incidentLoad (edgesTP σt xr) (Sum.inl r) =
      4 * (univ.filter fun j => xr j = r).card := by
    rw [edgesTP, (transformerData_P σt xr).incidentLoad_eq, card_xP_root]
    · intro p; simp [auxP]
    · rintro ⟨j, k⟩; fin_cases k <;> simp [petalV]
  rw [hP1, hP2, hTP]
  ring

end PartitionedTriangleAbsorption.PrivateTemplate
