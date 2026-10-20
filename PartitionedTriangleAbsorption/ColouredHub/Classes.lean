/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ColouredHub.Transformers

/-! # Coloured hubs IV: edge classes separating the nine blocks

Each vertex gets a class (original `0`, hubs `2`, tagged vertices by `PrivateTemplate.tagCls`),
and each edge the unordered pair of classes of its ends. The class pairs of the blocks
`P, P₁, P₂, T_P, J, T_Q, Q₂, Q₁, Q` are pairwise distinct, exactly as in the ordinary
template (`PrivateTemplate.pieceId` is reused), so the blocks are pairwise disjoint.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ColouredHub

open Finset PrivateTemplate TypedTransformer

variable {t : ℕ} {V : Type*} {m : ℕ} {T : Type*}

/-- Class of a vertex: original `0`, hub `2`, tagged by `tagCls`. -/
def hcls : HV V m t → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inr _) => 2
  | Sum.inr (Sum.inl (_, g)) => tagCls g

/-- The unordered pair of classes of the ends of an edge. -/
def hkappa (e : Sym2 (HV V m t)) : ℕ × ℕ :=
  Sym2.lift ⟨fun u w => (min (hcls u) (hcls w), max (hcls u) (hcls w)), fun u w => by
    simp [min_comm, max_comm]⟩ e

@[simp] theorem hkappa_mk (u w : HV V m t) :
    hkappa s(u, w) = (min (hcls u) (hcls w), max (hcls u) (hcls w)) := rfl

/-- Edges whose block identifier lies in `S`. -/
def HPieceIn (X : Finset (Sym2 (HV V m t))) (S : Finset ℕ) : Prop :=
  ∀ e ∈ X, pieceId (hkappa e) ∈ S

variable [DecidableEq V]

theorem HPieceIn.union {X Y : Finset (Sym2 (HV V m t))} {S S' : Finset ℕ} (hX : HPieceIn X S)
    (hY : HPieceIn Y S') : HPieceIn (X ∪ Y) (S ∪ S') := by
  intro e he
  rcases mem_union.mp he with he | he
  exacts [mem_union_left _ (hX e he), mem_union_right _ (hY e he)]

omit [DecidableEq V] in
theorem HPieceIn.disjoint {X Y : Finset (Sym2 (HV V m t))} {S S' : Finset ℕ}
    (hX : HPieceIn X S) (hY : HPieceIn Y S') (h : Disjoint S S') : Disjoint X Y :=
  Finset.disjoint_left.mpr fun e he he' =>
    Finset.disjoint_left.mp h (hX e he) (hY e he')

omit [DecidableEq V] in
theorem hkappa_fst_of_old (v : V) {e : Sym2 (HV V m t)} (h : old v ∈ e) :
    (hkappa e).1 = 0 := by
  obtain ⟨u, rfl⟩ := Sym2.mem_iff_exists.mp h
  simp [hcls]

variable (p : V → Fin t) (σ : Equiv.Perm (Fin m)) (X : Fin m → V)
  (w : T → Fin 3 → Fin t) (π : Fin m ≃ T × Fin 3)

/-- Close a class computation. -/
local macro "kcls" : tactic =>
  `(tactic| simp [hcls, tagCls])

theorem hkappa_P : ∀ e ∈ blkP (t := t) σ X, hkappa e = (0, 0) := by
  intro e he
  obtain ⟨j, rfl⟩ := mem_posEdges.mp he
  kcls

theorem hkappa_P1 : ∀ e ∈ blkP1 (t := t) σ X, hkappa e = (0, 3) := by
  intro e he
  rcases mem_union.mp he with he | he <;> obtain ⟨j, rfl⟩ := mem_posEdges.mp he <;> kcls

theorem hkappa_P2 : ∀ e ∈ blkP2 (t := t) σ X, hkappa e = (0, 4) ∨ hkappa e = (3, 4) := by
  intro e he
  rw [blkP2, pathP, mem_srcEdges_fourPath] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> kcls

theorem hkappa_J : ∀ e ∈ blkJ p σ X, hkappa e = (2, 2) := by
  intro e he
  rw [blkJ, pathJ, mem_srcEdges_fourPath] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> kcls

theorem hkappa_TP : ∀ e ∈ blkTP p σ X, (hkappa e).2 = 7 := by
  intro e he
  obtain ⟨q, u, rfl, hu⟩ := mem_transEdges_cases he
  have hq : hcls (auxTP (V := V) (t := t) q) = 7 := by simp [auxTP, hcls, tagCls]
  have hu7 : hcls u ≤ 7 := by
    rcases hu with ⟨⟨i, k⟩, rfl⟩ | ⟨⟨i, k⟩, rfl⟩ | ⟨q', rfl⟩
    · fin_cases k <;> simp [pathP, fourPath, hcls, tagCls]
    · fin_cases k <;> simp [pathJ, fourPath, hcls, tagCls]
    · simp [auxTP, hcls, tagCls]
  simp only [hkappa_mk, hq]
  omega

theorem hkappa_TQ : ∀ e ∈ blkTQ p X w π, (hkappa e).2 = 8 ∧ (hkappa e).1 ≠ 0 := by
  intro e he
  obtain ⟨q, u, rfl, hu⟩ := mem_transEdges_cases he
  have hq : hcls (auxTQ (V := V) (t := t) q) = 8 := by simp [auxTQ, hcls, tagCls]
  have hu8 : hcls u ≤ 8 ∧ hcls u ≠ 0 := by
    rcases hu with ⟨⟨i, k⟩, rfl⟩ | ⟨⟨i, k⟩, rfl⟩ | ⟨q', rfl⟩
    · fin_cases k <;> simp [pathQ, fourPath, hcls, tagCls]
    · unfold pathJQ
      split_ifs <;> fin_cases k <;> simp [pathJ, pathJrev, fourPath, hcls, tagCls]
    · simp [auxTQ, hcls, tagCls]
  simp only [hkappa_mk, hq]
  omega

theorem hkappa_Q2 : ∀ e ∈ blkQ2 (V := V) (t := t) π, hkappa e = (1, 6) ∨ hkappa e = (5, 6) := by
  intro e he
  rw [blkQ2, pathQ, mem_srcEdges_fourPath] at he
  obtain ⟨j, rfl | rfl | rfl | rfl⟩ := he <;> kcls

theorem hkappa_Q1 : ∀ e ∈ blkQ1 (V := V) (t := t) π, hkappa e = (1, 5) := by
  intro e he
  rcases mem_union.mp he with he | he <;> obtain ⟨j, rfl⟩ := mem_posEdges.mp he <;> kcls

theorem hkappa_Q : ∀ e ∈ blkQ (V := V) (t := t) π, hkappa e = (1, 1) := by
  intro e he
  obtain ⟨j, rfl⟩ := mem_posEdges.mp he
  kcls

theorem pieceIn_P : HPieceIn (blkP (t := t) σ X) {0} := fun e he => by
  simp [hkappa_P σ X e he, pieceId]

theorem pieceIn_P1 : HPieceIn (blkP1 (t := t) σ X) {1} := fun e he => by
  simp [hkappa_P1 σ X e he, pieceId]

theorem pieceIn_P2 : HPieceIn (blkP2 (t := t) σ X) {2} := fun e he => by
  rcases hkappa_P2 σ X e he with h | h <;> simp [h, pieceId]

theorem pieceIn_TP : HPieceIn (blkTP p σ X) {3} := fun e he => by
  simp [hkappa_TP p σ X e he, pieceId]

theorem pieceIn_J : HPieceIn (blkJ p σ X) {4} := fun e he => by
  simp [hkappa_J p σ X e he, pieceId]

theorem pieceIn_TQ : HPieceIn (blkTQ p X w π) {5} := fun e he => by
  simp [(hkappa_TQ p X w π e he).1, pieceId]

theorem pieceIn_Q2 : HPieceIn (blkQ2 (V := V) (t := t) π) {6} := fun e he => by
  rcases hkappa_Q2 π e he with h | h <;> simp [h, pieceId]

theorem pieceIn_Q1 : HPieceIn (blkQ1 (V := V) (t := t) π) {7} := fun e he => by
  simp [hkappa_Q1 π e he, pieceId]

theorem pieceIn_Q : HPieceIn (blkQ (V := V) (t := t) π) {8} := fun e he => by
  simp [hkappa_Q π e he, pieceId]

theorem pieceIn_hubTemplate :
    HPieceIn (hubTemplate p σ X w π) {1, 2, 3, 4, 5, 6, 7, 8} := by
  have h := ((((((pieceIn_P1 σ X).union (pieceIn_P2 σ X)).union (pieceIn_TP p σ X)).union
    (pieceIn_J p σ X)).union (pieceIn_TQ p X w π)).union (pieceIn_Q2 π)).union (pieceIn_Q1 π)
    |>.union (pieceIn_Q π)
  intro e he
  have := h e he
  simp only [mem_union, mem_singleton] at this
  simp only [mem_insert, mem_singleton]
  omega

/-- **No template edge joins two original vertices.** -/
theorem hubTemplate_no_old_edge (u v : V) :
    s((old u : HV V m t), old v) ∉ hubTemplate p σ X w π := by
  intro h
  have := pieceIn_hubTemplate p σ X w π _ h
  simp [hcls, pieceId] at this

theorem disjoint_hubTemplate_P : Disjoint (hubTemplate p σ X w π) (blkP σ X) :=
  (pieceIn_hubTemplate p σ X w π).disjoint (pieceIn_P σ X) (by decide)

end PartitionedTriangleAbsorption.ColouredHub
