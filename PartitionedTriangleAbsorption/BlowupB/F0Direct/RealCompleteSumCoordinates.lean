/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteSumModel
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealInternalInverse

@[expose] public section

/-! # The physical incidence table of every complete-crossing mixed graph -/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete.SumModel

open Finset TypedNibble TypedApplicationLinks TypedLoadNecessity TypedLoadFamilies
  TypedLoadCounterexample F0RigidBoost
open BalancedLinearRepair

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
variable (G : SimpleGraph A) (H : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

@[simp] theorem edgeEquiv_val (j : EdgeIndex G H) :
    (edgeEquiv G H j).val = rawEdge G H j := rfl

theorem chargeA (f : HostEdge G) : gFun part (rawEdge G H (Sum.inl f)) = -4 := by
  rcases f with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
    simp only [rawEdge, Sym2.map_mk, gFun, pairFun_pairVec_mk]
    norm_num [part, groupPair, g0]

theorem chargeB (f : HostEdge H) : gFun part (rawEdge G H (Sum.inr (Sum.inl f))) = -4 := by
  rcases f with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ u v =>
    simp only [rawEdge, Sym2.map_mk, gFun, pairFun_pairVec_mk]
    norm_num [part, groupPair, g0]

theorem chargeC (uv : A × B) : gFun part (rawEdge G H (Sum.inr (Sum.inr uv))) = 2 := by
  simp only [rawEdge, gFun, pairFun_pairVec_mk]
  norm_num [part, groupPair, g0]

theorem incidence_aa (f : HostEdge G) (gv : HostEdge G × B) :
    rawEdge G H (Sum.inl f) ∈ triEdges (triangle G H (Sum.inl gv)) ↔ f = gv.1 := by
  rcases f with ⟨e, he⟩
  rcases gv with ⟨⟨f, hf⟩, b⟩
  induction e using Sym2.ind with
  | _ u v =>
    induction f using Sym2.ind with
    | _ x y =>
      have huv : u ≠ v := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)
      have hxy : x ≠ y := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp hf)
      rw [triangleA_formula]
      simp only [rawEdge, Sym2.map_mk, mem_triEdges_iff, mem_insert, mem_singleton,
        Sum.inl.injEq, Sum.inl_ne_inr, or_false, Subtype.mk.injEq, Sym2.eq_iff]
      aesop

theorem incidence_ab (f : HostEdge G) (ug : A × HostEdge H) :
    rawEdge G H (Sum.inl f) ∉ triEdges (triangle G H (Sum.inr ug)) := by
  rcases f with ⟨e, he⟩
  rcases ug with ⟨a,⟨f,hf⟩⟩
  induction e using Sym2.ind with
  | _ u v =>
    induction f using Sym2.ind with
    | _ x y =>
      have huv : u ≠ v := G.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)
      rw [triangleB_formula]
      simp only [rawEdge, Sym2.map_mk, mem_triEdges_iff, mem_insert, mem_singleton,
        Sum.inl.injEq, Sum.inl_ne_inr, or_false]
      aesop

theorem incidence_ba (f : HostEdge H) (gv : HostEdge G × B) :
    rawEdge G H (Sum.inr (Sum.inl f)) ∉ triEdges (triangle G H (Sum.inl gv)) := by
  rcases f with ⟨e, he⟩
  rcases gv with ⟨⟨f,hf⟩, b⟩
  induction e using Sym2.ind with
  | _ u v =>
    induction f using Sym2.ind with
    | _ x y =>
      have huv : u ≠ v := H.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)
      rw [triangleA_formula]
      simp only [rawEdge, Sym2.map_mk, mem_triEdges_iff, mem_insert, mem_singleton,
        Sum.inr.injEq, Sum.inr_ne_inl, false_or]
      aesop

theorem incidence_bb (f : HostEdge H) (ug : A × HostEdge H) :
    rawEdge G H (Sum.inr (Sum.inl f)) ∈ triEdges (triangle G H (Sum.inr ug)) ↔ f = ug.2 := by
  rcases f with ⟨e, he⟩
  rcases ug with ⟨a,⟨f,hf⟩⟩
  induction e using Sym2.ind with
  | _ u v =>
    induction f using Sym2.ind with
    | _ x y =>
      have huv : u ≠ v := H.ne_of_adj (SimpleGraph.mem_edgeFinset.mp he)
      have hxy : x ≠ y := H.ne_of_adj (SimpleGraph.mem_edgeFinset.mp hf)
      rw [triangleB_formula]
      simp only [rawEdge, Sym2.map_mk, mem_triEdges_iff, mem_insert, mem_singleton,
        Sum.inr.injEq, Sum.inr_ne_inl, false_or, Subtype.mk.injEq, Sym2.eq_iff]
      aesop

theorem incidence_ca (uv : A × B) (fv : HostEdge G × B) :
    edgeIndicator (rawEdge G H (Sum.inr (Sum.inr uv))) (triangle G H (Sum.inl fv)) =
      if uv.2 = fv.2 then Internal.matrix G uv.1 fv.1 else 0 := by
  rcases uv with ⟨a,b⟩
  rcases fv with ⟨⟨f,hf⟩,c⟩
  induction f using Sym2.ind with
  | _ x y =>
    have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp hf
    rw [triangleA_formula]
    by_cases hax : a = x <;> by_cases hay : a = y <;> by_cases hbc : b = c <;>
      simp [rawEdge, edgeIndicator, mem_triEdges_iff, Internal.matrix,
        SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff,
        hxy, hax, hay, hbc]

theorem incidence_cb (uv : A × B) (uf : A × HostEdge H) :
    edgeIndicator (rawEdge G H (Sum.inr (Sum.inr uv))) (triangle G H (Sum.inr uf)) =
      if uv.1 = uf.1 then Internal.matrix H uv.2 uf.2 else 0 := by
  rcases uv with ⟨a,b⟩
  rcases uf with ⟨c,⟨f,hf⟩⟩
  induction f using Sym2.ind with
  | _ x y =>
    have hxy : H.Adj x y := SimpleGraph.mem_edgeFinset.mp hf
    rw [triangleB_formula]
    by_cases hbx : b = x <;> by_cases hby : b = y <;> by_cases hac : a = c <;>
      simp [rawEdge, edgeIndicator, mem_triEdges_iff, Internal.matrix,
        SimpleGraph.incMatrix_apply', SimpleGraph.mk'_mem_incidenceSet_iff,
        hxy, hbx, hby, hac]

/-- Produced from the two actual internal graphs: this is not an assumed
coordinate table.  All crossing edges are present in `joined G H`. -/
noncomputable def coordinates :
    Coordinates part (joined G H) (Internal.matrix G) (Internal.matrix H) where
  edge := edgeEquiv G H
  tri := triangle G H
  tri_mem := triangle_mem G H
  tri_injective := triangle_injective G H
  chargeA := chargeA G H
  chargeB := chargeB G H
  chargeC := chargeC G H
  aa := incidence_aa G H
  ab := incidence_ab G H
  ba := incidence_ba G H
  bb := incidence_bb G H
  ca := incidence_ca G H
  cb := incidence_cb G H

#print axioms coordinates

end PartitionedTriangleAbsorption.F0Direct.RealComplete.SumModel
