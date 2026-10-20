/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteCoordinates
import Mathlib.Combinatorics.SimpleGraph.IncMatrix
import Mathlib.Data.Finset.Sum

/-! # The actual complete-crossing graph and its physical coordinate sets -/

namespace PartitionedTriangleAbsorption.F0Direct.RealComplete.SumModel

open Finset TypedNibble TypedApplicationLinks TypedLoadNecessity F0RigidBoost
open BalancedLinearRepair

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

def joined (G : SimpleGraph A) (H : SimpleGraph B) : SimpleGraph (A ⊕ B) where
  Adj
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inr u, Sum.inr v => H.Adj u v
    | _, _ => True
  symm.symm
    | Sum.inl _, Sum.inl _ => G.adj_symm
    | Sum.inr _, Sum.inr _ => H.adj_symm
    | Sum.inl _, Sum.inr _ | Sum.inr _, Sum.inl _ => id
  loopless.irrefl
    | Sum.inl u => G.loopless.irrefl u
    | Sum.inr v => H.loopless.irrefl v

instance joined_decidable (G : SimpleGraph A) (H : SimpleGraph B)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (joined G H).Adj :=
  fun u v => by cases u <;> cases v <;> dsimp [joined] <;> infer_instance

def part : A ⊕ B → Fin 2 := Sum.elim (fun _ => 0) (fun _ => 1)

variable (G : SimpleGraph A) (H : SimpleGraph B)
variable [DecidableRel G.Adj] [DecidableRel H.Adj]

abbrev EdgeIndex := HostEdge G ⊕ (HostEdge H ⊕ (A × B))
abbrev TriIndex := (HostEdge G × B) ⊕ (A × HostEdge H)

def rawEdge : EdgeIndex G H → Sym2 (A ⊕ B)
  | Sum.inl f => Sym2.map Sum.inl f.val
  | Sum.inr (Sum.inl f) => Sym2.map Sum.inr f.val
  | Sum.inr (Sum.inr uv) => s(Sum.inl uv.1, Sum.inr uv.2)

theorem rawEdge_mem (j : EdgeIndex G H) : rawEdge G H j ∈ (joined G H).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset]
  rcases j with ⟨f, hf⟩ | ⟨f, hf⟩ | uv
  · induction f using Sym2.ind with
    | _ u v =>
      change G.Adj u v
      exact SimpleGraph.mem_edgeFinset.mp hf
  · induction f using Sym2.ind with
    | _ u v =>
      change H.Adj u v
      exact SimpleGraph.mem_edgeFinset.mp hf
  · trivial

theorem inl_edge_ne_inr_edge (e : Sym2 A) (f : Sym2 B) :
    Sym2.map (Sum.inl : A → A ⊕ B) e ≠ Sym2.map Sum.inr f := by
  induction e using Sym2.ind with
  | _ u v =>
    induction f using Sym2.ind with
    | _ x y => simp [Sym2.map_mk, Sym2.eq_iff]

theorem inl_edge_ne_cross (e : Sym2 A) (uv : A × B) :
    Sym2.map (Sum.inl : A → A ⊕ B) e ≠ s(Sum.inl uv.1, Sum.inr uv.2) := by
  induction e using Sym2.ind with
  | _ u v => simp [Sym2.map_mk, Sym2.eq_iff]

theorem inr_edge_ne_cross (e : Sym2 B) (uv : A × B) :
    Sym2.map (Sum.inr : B → A ⊕ B) e ≠ s(Sum.inl uv.1, Sum.inr uv.2) := by
  induction e using Sym2.ind with
  | _ u v => simp [Sym2.map_mk, Sym2.eq_iff]

theorem rawEdge_injective : Function.Injective (rawEdge G H) := by
  intro i j hij
  rcases i with f | f | uv <;> rcases j with g | g | xy
  · congr 1
    apply Subtype.ext
    exact Sym2.map.injective Sum.inl_injective hij
  · exact False.elim (inl_edge_ne_inr_edge f.val g.val hij)
  · exact False.elim (inl_edge_ne_cross f.val xy hij)
  · exact False.elim (inl_edge_ne_inr_edge g.val f.val hij.symm)
  · congr 2
    apply Subtype.ext
    exact Sym2.map.injective Sum.inr_injective hij
  · exact False.elim (inr_edge_ne_cross f.val xy hij)
  · exact False.elim (inl_edge_ne_cross g.val uv hij.symm)
  · exact False.elim (inr_edge_ne_cross g.val uv hij.symm)
  · change s(Sum.inl uv.1, Sum.inr uv.2) = s(Sum.inl xy.1, Sum.inr xy.2) at hij
    simp only [Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
      Sum.inr_ne_inl, and_self, or_false] at hij
    congr 2
    exact Prod.ext hij.1 hij.2

def edgeMap (j : EdgeIndex G H) : HostEdge (joined G H) := ⟨rawEdge G H j, rawEdge_mem G H j⟩

theorem edgeMap_bijective : Function.Bijective (edgeMap G H) := by
  constructor
  · intro i j hij
    exact rawEdge_injective G H (congrArg Subtype.val hij)
  · rintro ⟨e, he⟩
    have he' : e ∈ (joined G H).edgeSet := SimpleGraph.mem_edgeFinset.mp he
    induction e using Sym2.ind with
    | _ u v =>
      cases u with
      | inl a =>
        cases v with
        | inl b =>
          have hab : s(a,b) ∈ G.edgeFinset := by
            exact SimpleGraph.mem_edgeFinset.mpr he'
          exact ⟨Sum.inl ⟨s(a,b), hab⟩, rfl⟩
        | inr b => exact ⟨Sum.inr (Sum.inr (a,b)), rfl⟩
      | inr a =>
        cases v with
        | inl b =>
          refine ⟨Sum.inr (Sum.inr (b,a)), ?_⟩
          apply Subtype.ext
          exact Sym2.eq_swap
        | inr b =>
          have hab : s(a,b) ∈ H.edgeFinset := by
            exact SimpleGraph.mem_edgeFinset.mpr he'
          exact ⟨Sum.inr (Sum.inl ⟨s(a,b), hab⟩), rfl⟩

noncomputable def edgeEquiv : EdgeIndex G H ≃ HostEdge (joined G H) :=
  Equiv.ofBijective (edgeMap G H) (edgeMap_bijective G H)

def triangle : TriIndex G H → Finset (A ⊕ B)
  | Sum.inl fv => insert (Sum.inr fv.2) (fv.1.val.toFinset.map Function.Embedding.inl)
  | Sum.inr uf => insert (Sum.inl uf.1) (uf.2.val.toFinset.map Function.Embedding.inr)

theorem triangleA_formula {u v : A} (h : s(u,v) ∈ G.edgeFinset) (b : B) :
    triangle G H (Sum.inl (⟨s(u,v), h⟩, b)) = {Sum.inl u, Sum.inl v, Sum.inr b} := by
  simp [triangle, Sym2.toFinset_mk_eq]
  ext x
  simp only [mem_insert, mem_singleton]
  tauto

theorem triangleB_formula (a : A) {u v : B} (h : s(u,v) ∈ H.edgeFinset) :
    triangle G H (Sum.inr (a, ⟨s(u,v), h⟩)) = {Sum.inl a, Sum.inr u, Sum.inr v} := by
  simp [triangle, Sym2.toFinset_mk_eq]

theorem triangle_mem (i : TriIndex G H) : triangle G H i ∈ copies part F0 (joined G H) := by
  rcases i with ⟨⟨f,hf⟩,b⟩ | ⟨a,⟨f,hf⟩⟩
  · induction f using Sym2.ind with
    | _ u v =>
      rw [triangleA_formula]
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.mp hf
      apply mem_copies_iff.mpr
      refine ⟨SimpleGraph.is3Clique_triple_iff.mpr ⟨huv, trivial, trivial⟩, ?_⟩
      rw [map_three part (by simpa using G.ne_of_adj huv) (by simp) (by simp)]
      dsimp [part]
      decide
  · induction f using Sym2.ind with
    | _ u v =>
      rw [triangleB_formula]
      have huv : H.Adj u v := SimpleGraph.mem_edgeFinset.mp hf
      apply mem_copies_iff.mpr
      refine ⟨SimpleGraph.is3Clique_triple_iff.mpr ⟨trivial, trivial, huv⟩, ?_⟩
      rw [map_three part (by simp) (by simp) (by simpa using H.ne_of_adj huv)]
      dsimp [part]
      decide

theorem triangleA_left (f : HostEdge G) (b : B) :
    (triangle G H (Sum.inl (f,b))).toLeft = f.val.toFinset := by
  ext a
  simp [triangle]

theorem triangleA_right (f : HostEdge G) (b : B) :
    (triangle G H (Sum.inl (f,b))).toRight = {b} := by
  ext a
  simp [triangle]

theorem triangleB_left (a : A) (f : HostEdge H) :
    (triangle G H (Sum.inr (a,f))).toLeft = {a} := by
  ext b
  simp [triangle]

theorem triangleB_right (a : A) (f : HostEdge H) :
    (triangle G H (Sum.inr (a,f))).toRight = f.val.toFinset := by
  ext b
  simp [triangle]

theorem toFinset_injective : Function.Injective (Sym2.toFinset : Sym2 A → Finset A) := by
  intro e f h
  apply Sym2.ext
  intro a
  simpa only [← Sym2.mem_toFinset, h]

theorem triangle_injective : Function.Injective (triangle G H) := by
  intro i j hij
  rcases i with ⟨f,b⟩ | ⟨a,f⟩ <;> rcases j with ⟨g,c⟩ | ⟨d,g⟩
  · have hL := congrArg Finset.toLeft hij
    have hR := congrArg Finset.toRight hij
    simp only [triangleA_left, triangleA_right, singleton_inj] at hL hR
    have hfg : f = g := Subtype.ext (toFinset_injective hL)
    subst g
    subst c
    rfl
  · have hL := congrArg (fun s => s.toLeft.card) hij
    rw [triangleA_left, triangleB_left, card_singleton,
      Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp f.property))] at hL
    omega
  · have hR := congrArg (fun s => s.toRight.card) hij
    rw [triangleB_right, triangleA_right, card_singleton,
      Sym2.card_toFinset_of_not_isDiag _ (H.not_isDiag_of_mem_edgeSet
        (SimpleGraph.mem_edgeFinset.mp f.property))] at hR
    omega
  · have hL := congrArg Finset.toLeft hij
    have hR := congrArg Finset.toRight hij
    simp only [triangleB_left, triangleB_right, singleton_inj] at hL hR
    have hfg : f = g := Subtype.ext (toFinset_injective hR)
    subst g
    subst d
    rfl

#print axioms edgeMap_bijective
#print axioms triangle_mem
#print axioms triangle_injective

end PartitionedTriangleAbsorption.F0Direct.RealComplete.SumModel
