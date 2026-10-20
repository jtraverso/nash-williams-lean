/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Decomp

/-! # Coloured hubs VI: exact counts

* `|A| = 2m + 4m + 44m + 4m + 44m + 4m + 2m + m = 105 m`;
* an original vertex `v` meets `8 · #{i | X i = v}` edges of `A`, which is `4 d_P(v)` for a
  closed-trail system (`ColouredHub.Main`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate TypedTransformer AntiEdgeSelection OnePart

variable {t : ℕ} {V : Type*} [DecidableEq V] {m : ℕ} {T : Type*}
variable {p : V → Fin t} {σ : Equiv.Perm (Fin m)} {X : Fin m → V}
  {w : T → Fin 3 → Fin t} {π : Fin m ≃ T × Fin 3}

/-! ### Block cardinalities -/

theorem card_blkP1 (hne : ∀ i, X i ≠ X (σ i)) : (blkP1 (t := t) σ X).card = 2 * m := by
  rw [blkP1, card_union_of_disjoint, card_posEdges, card_posEdges, Fintype.card_fin]
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

omit [DecidableEq V] in
theorem pathP_edge_injective :
    Function.Injective fun z => s(pathP (t := t) X z, pathP X (blowPerm σ z)) := by
  rintro ⟨j, k⟩ ⟨j', k'⟩ h
  fin_cases k <;> fin_cases k' <;> simp [pathP, fourPath] at h ⊢ <;> simp_all

theorem card_blkP2 : (blkP2 (t := t) σ X).card = 4 * m := by
  rw [blkP2, srcEdges, card_posEdges pathP_edge_injective, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, mul_comm]

theorem card_blkTP : (blkTP p σ X).card = 44 * m := by
  rw [blkTP, tdata_P.card_transEdges, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  ring

theorem card_blkJ : (blkJ p σ X).card = 4 * m := by
  rw [blkJ, srcEdges, card_posEdges (tdata_P (p := p) (σ := σ) (X := X)).hyinj,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm]

theorem card_blkTQ (hM : Matched p σ X w π) : (blkTQ p X w π).card = 44 * m := by
  rw [blkTQ, (tdata_Q hM).card_transEdges, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]
  ring

theorem card_blkQ2 (hM : Matched p σ X w π) : (blkQ2 (V := V) (t := t) π).card = 4 * m := by
  rw [blkQ2, (tdata_Q hM).card_srcEdges, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin, mul_comm]

theorem card_blkQ1 : (blkQ1 (V := V) (t := t) π).card = 2 * m := by
  rw [blkQ1, card_union_of_disjoint, card_posEdges, card_posEdges, Fintype.card_fin]
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
    · exact qPerm_ne π j h1.symm

theorem card_blkQ : (blkQ (V := V) (t := t) π).card = m := by
  rw [blkQ, card_posEdges qEdge_injective', Fintype.card_fin]

/-- **Edge count.** The coloured-hub template has exactly `105 m` edges. -/
theorem card_hubTemplate (hne : ∀ i, X i ≠ X (σ i)) (hM : Matched p σ X w π) :
    (hubTemplate p σ X w π).card = 105 * m := by
  have i1 := pieceIn_P1 (t := t) σ X
  have i2 := pieceIn_P2 (t := t) σ X
  have i3 := pieceIn_TP p σ X
  have i4 := pieceIn_J p σ X
  have i5 := pieceIn_TQ p X w π
  have i6 := pieceIn_Q2 (V := V) (t := t) π
  have i7 := pieceIn_Q1 (V := V) (t := t) π
  have i8 := pieceIn_Q (V := V) (t := t) π
  rw [hubTemplate, card_union_of_disjoint (((((((i1.union i2).union i3).union i4).union
      i5).union i6).union i7).disjoint i8 (by decide)),
    card_union_of_disjoint ((((((i1.union i2).union i3).union i4).union i5).union i6).disjoint
      i7 (by decide)),
    card_union_of_disjoint (((((i1.union i2).union i3).union i4).union i5).disjoint i6
      (by decide)),
    card_union_of_disjoint ((((i1.union i2).union i3).union i4).disjoint i5 (by decide)),
    card_union_of_disjoint (((i1.union i2).union i3).disjoint i4 (by decide)),
    card_union_of_disjoint ((i1.union i2).disjoint i3 (by decide)),
    card_union_of_disjoint (i1.disjoint i2 (by decide)),
    card_blkP1 hne, card_blkP2, card_blkTP, card_blkJ, card_blkTQ hM,
    card_blkQ2 hM, card_blkQ1, card_blkQ]
  ring

/-! ### Degrees of original vertices -/

theorem incidentLoad_old_eq_zero {Y : Finset (Sym2 (HV V m t))}
    (hY : ∀ e ∈ Y, (hkappa e).1 ≠ 0) (v : V) : incidentLoad Y (old v) = 0 := by
  unfold incidentLoad
  rw [card_eq_zero, filter_eq_empty_iff]
  intro e he hv
  exact hY e he (hkappa_fst_of_old v hv)

omit [DecidableEq V] in
theorem card_pathP_old [DecidableEq V] (v : V) :
    (univ.filter fun z => pathP (t := t) X z = old v).card =
      (univ.filter fun i => X i = v).card := by
  symm
  apply card_bij (fun j _ => (j, (0 : Fin 4)))
  · intro j hj
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    simpa only [pathP, fourPath_zero, Sum.inl.injEq] using (mem_filter.mp hj).2
  · intro j _ j' _ h; simpa using h
  · rintro ⟨j, k⟩ hk
    simp only [mem_filter, mem_univ, true_and] at hk
    fin_cases k
    · exact ⟨j, mem_filter.mpr ⟨mem_univ _, Sum.inl.inj hk⟩, rfl⟩
    · cases hk
    · cases hk
    · cases hk

/-- **Root degree.** An original vertex meets `8 · #{i | X i = v}` template edges. -/
theorem incidentLoad_hubTemplate_old (hne : ∀ i, X i ≠ X (σ i)) (v : V) :
    incidentLoad (hubTemplate p σ X w π) (old v) = 8 * (univ.filter fun i => X i = v).card := by
  have i1 := pieceIn_P1 (t := t) σ X
  have i2 := pieceIn_P2 (t := t) σ X
  have i3 := pieceIn_TP p σ X
  have i4 := pieceIn_J p σ X
  have i5 := pieceIn_TQ p X w π
  have i6 := pieceIn_Q2 (V := V) (t := t) π
  have i7 := pieceIn_Q1 (V := V) (t := t) π
  have i8 := pieceIn_Q (V := V) (t := t) π
  rw [hubTemplate, incidentLoad_union (((((((i1.union i2).union i3).union i4).union i5).union
      i6).union i7).disjoint i8 (by decide)),
    incidentLoad_union ((((((i1.union i2).union i3).union i4).union i5).union i6).disjoint
      i7 (by decide)),
    incidentLoad_union (((((i1.union i2).union i3).union i4).union i5).disjoint i6
      (by decide)),
    incidentLoad_union ((((i1.union i2).union i3).union i4).disjoint i5 (by decide)),
    incidentLoad_union (((i1.union i2).union i3).disjoint i4 (by decide)),
    incidentLoad_union ((i1.union i2).disjoint i3 (by decide)),
    incidentLoad_union (i1.disjoint i2 (by decide))]
  rw [incidentLoad_old_eq_zero (Y := blkJ p σ X) (fun e he => by simp [hkappa_J p σ X e he]),
    incidentLoad_old_eq_zero (Y := blkTQ p X w π) (fun e he => (hkappa_TQ p X w π e he).2),
    incidentLoad_old_eq_zero (Y := blkQ2 π)
      (fun e he => by rcases hkappa_Q2 π e he with h | h <;> simp [h]),
    incidentLoad_old_eq_zero (Y := blkQ1 π) (fun e he => by simp [hkappa_Q1 π e he]),
    incidentLoad_old_eq_zero (Y := blkQ π) (fun e he => by simp [hkappa_Q π e he])]
  have hP1 : incidentLoad (blkP1 (t := t) σ X) (old v) =
      2 * (univ.filter fun i => X i = v).card := by
    have hd : Disjoint (posEdges (fun i => (old (X i) : HV V m t)) fun i => ax i .p1)
        (posEdges (fun i => ax i .p1) fun i => old (X (σ i))) := by
      rw [Finset.disjoint_left]
      intro e he he'
      obtain ⟨j, rfl⟩ := mem_posEdges.mp he
      obtain ⟨j', h⟩ := mem_posEdges.mp he'
      simp only [Sym2.eq_iff, reduceCtorEq, false_and, Sum.inl.injEq, Sum.inr.injEq,
        Prod.mk.injEq, and_true, false_or] at h
      obtain ⟨h1, rfl⟩ := h
      exact hne j h1
    rw [blkP1, incidentLoad_union hd, incidentLoad_posEdges, incidentLoad_posEdges]
    · simp only [Sum.inl.injEq, reduceCtorEq, filter_false, card_empty, add_zero, zero_add]
      rw [card_filter_perm σ X v]
      ring
    · intro j j' h; aesop
    · intro j; simp
    · intro j j' h; aesop
    · intro j; simp
  have hP2 : incidentLoad (blkP2 (t := t) σ X) (old v) =
      2 * (univ.filter fun i => X i = v).card := by
    have hT := tdata_P (p := p) (σ := σ) (X := X)
    rw [blkP2, srcEdges, incidentLoad_posEdges hT.hxinj hT.hx,
      card_filter_perm (blowPerm σ) (pathP X), card_pathP_old]
    ring
  have hTP : incidentLoad (blkTP p σ X) (old v) = 4 * (univ.filter fun i => X i = v).card := by
    rw [blkTP, tdata_P.incidentLoad_eq, card_pathP_old]
    · intro q; simp [auxTP]
    · rintro ⟨j, k⟩; fin_cases k <;> simp [pathJ, fourPath]
  rw [hP1, hP2, hTP]
  ring

end PartitionedTriangleAbsorption.ColouredHub
