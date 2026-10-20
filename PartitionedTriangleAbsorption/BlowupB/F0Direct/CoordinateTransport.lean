/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteCoordinates
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.UniformWeights

@[expose] public section

/-! # Transport of physical complete-crossing coordinates by a vertex equivalence

The partition labels may be exchanged.  Only equality of the two endpoint
labels is preserved, which is precisely what the mixed-triangle family and
its balance functional require.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.CoordinateTransport

open Finset TypedNibble TypedApplicationLinks TypedLoadNecessity TypedLoadFamilies
  TypedLoadCounterexample F0RigidBoost
open PartitionedTriangleAbsorption.F0Direct.BalancedLinearRepair
open PartitionedTriangleAbsorption.F0Direct.RealComplete

variable {U V : Type*} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]

def sym2Equiv (e : U ≃ V) : Sym2 U ≃ Sym2 V where
  toFun := Sym2.map e
  invFun := Sym2.map e.symm
  left_inv f := by induction f using Sym2.ind with | _ u v => simp
  right_inv f := by induction f using Sym2.ind with | _ u v => simp

theorem edge_mem_map (K : SimpleGraph U) (J : SimpleGraph V)
    [DecidableRel K.Adj] [DecidableRel J.Adj] (e : U ≃ V)
    (hAdj : ∀ u v, K.Adj u v ↔ J.Adj (e u) (e v)) (f : Sym2 U) :
    f ∈ K.edgeFinset ↔ Sym2.map e f ∈ J.edgeFinset := by
  induction f using Sym2.ind with
  | _ u v =>
    simpa only [Sym2.map_mk, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using hAdj u v

def edgeEquiv (K : SimpleGraph U) (J : SimpleGraph V)
    [DecidableRel K.Adj] [DecidableRel J.Adj] (e : U ≃ V)
    (hAdj : ∀ u v, K.Adj u v ↔ J.Adj (e u) (e v)) : HostEdge K ≃ HostEdge J :=
  (sym2Equiv e).subtypeEquiv (edge_mem_map K J e hAdj)

@[simp] theorem edgeEquiv_val (K : SimpleGraph U) (J : SimpleGraph V)
    [DecidableRel K.Adj] [DecidableRel J.Adj] (e : U ≃ V)
    (hAdj : ∀ u v, K.Adj u v ↔ J.Adj (e u) (e v)) (f : HostEdge K) :
    (edgeEquiv K J e hAdj f).val = Sym2.map e f.val := rfl

theorem gFun_mk (p : V → Fin 2) (u v : V) :
    gFun p s(u,v) = if p u = p v then -4 else 2 := by
  have h : ∀ i j : Fin 2, groupPair g0 i j + groupPair g0 j i =
      if i = j then (-4 : ℤ) else 2 := by decide
  simp only [gFun, pairFun_pairVec_mk, h, Int.cast_ite, Int.cast_neg,
    Int.cast_ofNat]

theorem gFun_map (q : U → Fin 2) (p : V → Fin 2) (e : U ≃ V)
    (hPart : ∀ u v, q u = q v ↔ p (e u) = p (e v)) (f : Sym2 U) :
    gFun p (Sym2.map e f) = gFun q f := by
  induction f using Sym2.ind with
  | _ u v => simp only [Sym2.map_mk, gFun_mk, ← hPart]

theorem triEdges_map_equiv (e : U ≃ V) (s : Finset U) :
    triEdges (s.map e.toEmbedding) = (triEdges s).map e.toEmbedding.sym2Map := by
  simp only [map_eq_image, triEdges, sym2_image, filter_image,
    Sym2.isDiag_map e.toEmbedding.injective]
  rfl

@[simp] theorem edge_mem_tri_map (e : U ≃ V) (f : Sym2 U) (s : Finset U) :
    Sym2.map e f ∈ triEdges (s.map e.toEmbedding) ↔ f ∈ triEdges s := by
  rw [triEdges_map_equiv]
  exact mem_map' e.toEmbedding.sym2Map

theorem copy_map (q : U → Fin 2) (p : V → Fin 2)
    (K : SimpleGraph U) (J : SimpleGraph V) (e : U ≃ V)
    (hAdj : ∀ u v, K.Adj u v ↔ J.Adj (e u) (e v))
    (hPart : ∀ u v, q u = q v ↔ p (e u) = p (e v))
    (s : Finset U) (hs : IsCopy q F0 K s) : IsCopy p F0 J (s.map e.toEmbedding) := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp hs.1.card_eq
  have hK := SimpleGraph.is3Clique_triple_iff.mp hs.1
  have hF := hs.2
  rw [map_three q hab hac hbc] at hF
  have hMixed := (triple_F0_iff _ _ _).mp hF
  simp only [map_insert, map_singleton, Equiv.coe_toEmbedding]
  apply IntegerCertificate.isCopy_of_adj ((hAdj a b).mp hK.1)
    ((hAdj a c).mp hK.2.1) ((hAdj b c).mp hK.2.2)
  rintro ⟨hab',hbc'⟩
  exact hMixed ⟨(hPart a b).mpr hab',(hPart b c).mpr hbc'⟩

variable {A B EA EB : Type*} [Fintype A] [Fintype B] [Fintype EA] [Fintype EB]
  [DecidableEq A] [DecidableEq B]

/-- Transport the entire verified incidence table.  In particular this does
not assume a new coordinate table for the target graph. -/
noncomputable def coordinates (q : U → Fin 2) (p : V → Fin 2)
    (K : SimpleGraph U) (J : SimpleGraph V)
    [DecidableRel K.Adj] [DecidableRel J.Adj]
    (IA : A → EA → ℝ) (IB : B → EB → ℝ) (C : Coordinates q K IA IB)
    (e : U ≃ V) (hAdj : ∀ u v, K.Adj u v ↔ J.Adj (e u) (e v))
    (hPart : ∀ u v, q u = q v ↔ p (e u) = p (e v)) : Coordinates p J IA IB where
  edge := C.edge.trans (edgeEquiv K J e hAdj)
  tri i := (C.tri i).map e.toEmbedding
  tri_mem i := mem_copies_iff.mpr (copy_map q p K J e hAdj hPart _
    (mem_copies_iff.mp (C.tri_mem i)))
  tri_injective := (Finset.map_injective e.toEmbedding).comp C.tri_injective
  chargeA f := by
    change gFun p (Sym2.map e (C.edge (Sum.inl f)).val) = -4
    rw [gFun_map q p e hPart]
    exact C.chargeA f
  chargeB f := by
    change gFun p (Sym2.map e (C.edge (Sum.inr (Sum.inl f))).val) = -4
    rw [gFun_map q p e hPart]
    exact C.chargeB f
  chargeC uv := by
    change gFun p (Sym2.map e (C.edge (Sum.inr (Sum.inr uv))).val) = 2
    rw [gFun_map q p e hPart]
    exact C.chargeC uv
  aa f fv := by
    change Sym2.map e _ ∈ triEdges ((C.tri (Sum.inl fv)).map e.toEmbedding) ↔ _
    rw [edge_mem_tri_map]
    exact C.aa f fv
  ab f uf := by
    change Sym2.map e _ ∉ triEdges ((C.tri (Sum.inr uf)).map e.toEmbedding)
    rw [edge_mem_tri_map]
    exact C.ab f uf
  ba f fv := by
    change Sym2.map e _ ∉ triEdges ((C.tri (Sum.inl fv)).map e.toEmbedding)
    rw [edge_mem_tri_map]
    exact C.ba f fv
  bb f uf := by
    change Sym2.map e _ ∈ triEdges ((C.tri (Sum.inr uf)).map e.toEmbedding) ↔ _
    rw [edge_mem_tri_map]
    exact C.bb f uf
  ca uv fv := by
    change edgeIndicator (Sym2.map e _) ((C.tri (Sum.inl fv)).map e.toEmbedding) = _
    simpa only [edgeIndicator, edge_mem_tri_map] using C.ca uv fv
  cb uv uf := by
    change edgeIndicator (Sym2.map e _) ((C.tri (Sum.inr uf)).map e.toEmbedding) = _
    simpa only [edgeIndicator, edge_mem_tri_map] using C.cb uv uf

#print axioms coordinates

end PartitionedTriangleAbsorption.BlowupB.F0Direct.CoordinateTransport
