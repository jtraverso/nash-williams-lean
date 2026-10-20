/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Transformer
public import PartitionedTriangleAbsorption.ReturnedBridge

/-! # Decompositions assembled from groups of pairwise disjoint atoms

Generic in the type family `F`. If a family of pairwise edge-disjoint *atoms* is split into
groups whose unions are each decomposable, then the union of all atoms is decomposable.
Also: a typed triangle is decomposable, and an edge with both endpoints in a vertex set lies
in the triangle edge set of that set (used to rule out root-root edges).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

theorem empty_hasDecomp : HasDecomp p F (∅ : Finset (Sym2 V)) := ⟨∅, by simp [IsDecomp]⟩

/-- A union of pairwise disjoint decomposable edge sets is decomposable. -/
theorem hasDecomp_biUnion {I : Type*} (s : Finset I) (E : I → Finset (Sym2 V))
    (hdec : ∀ i ∈ s, HasDecomp p F (E i))
    (hdis : (s : Set I).PairwiseDisjoint E) :
    HasDecomp p F (s.biUnion E) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (empty_hasDecomp (p := p) (F := F))
  | insert a s ha ih =>
    rw [biUnion_insert]
    refine HasDecomp.union (hdec a (mem_insert_self _ _))
      (ih (fun i hi => hdec i (mem_insert_of_mem hi))
        (hdis.subset (by simp))) ?_
    rw [disjoint_biUnion_right]
    intro i hi
    exact hdis (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

/-- **Grouping principle.** Pairwise edge-disjoint atoms, grouped by `g`, with every group
union decomposable, have a decomposable total union. -/
theorem hasDecomp_of_groups {ι κ : Type*} [Fintype ι] [Finite κ] [DecidableEq κ]
    (a : ι → Finset (Sym2 V)) (g : ι → κ) (hdis : Pairwise fun i j => Disjoint (a i) (a j))
    (hgrp : ∀ k, HasDecomp p F ((univ.filter fun i => g i = k).biUnion a)) :
    HasDecomp p F (univ.biUnion a) := by
  let := Fintype.ofFinite κ
  have heq : univ.biUnion a =
      univ.biUnion (fun k => (univ.filter fun i => g i = k).biUnion a) := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, mem_filter]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨g i, i, rfl, hi⟩
    · rintro ⟨k, i, -, hi⟩; exact ⟨i, hi⟩
  rw [heq]
  refine hasDecomp_biUnion _ _ (fun k _ => hgrp k) ?_
  intro k _ k' _ hkk'
  simp only [Function.onFun]
  rw [disjoint_biUnion_left]
  intro i hi
  rw [disjoint_biUnion_right]
  intro j hj
  have hij : i ≠ j := by
    rintro rfl
    exact hkk' ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2)
  exact hdis hij

/-- A typed triangle is decomposable. -/
theorem hasDecomp_triEdges {s : Finset V} (h : IsTypedTri p F s) :
    HasDecomp p F (triEdges s) :=
  ⟨{s}, fun s' hs' => by rw [mem_singleton.mp hs']; exact h, by simp, by simp⟩

/-- An edge of a simple graph with both endpoints in `s` is an edge of the triangle set
`triEdges s`. -/
theorem mem_triEdges_of_endpoints {G : SimpleGraph V} {s : Finset V} {e : Sym2 V}
    (he : e ∈ G.edgeSet) (hs : ∀ x ∈ e, x ∈ s) : e ∈ triEdges s := by
  induction e using Sym2.ind with
  | _ x y =>
    simp only [triEdges, mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
    exact ⟨⟨hs x (Sym2.mem_mk_left x y), hs y (Sym2.mem_mk_right x y)⟩,
      G.ne_of_adj he⟩

/-- An edge belongs to the vertex set of any edge set containing it. -/
theorem mem_vertSet_of_mem [Fintype V] {E : Finset (Sym2 V)} {e : Sym2 V} (he : e ∈ E)
    {x : V} (hx : x ∈ e) : x ∈ vertSet E := by
  simp only [vertSet, mem_filter, mem_univ, true_and]
  exact ⟨e, he, hx⟩

/-- **Vertex localisation of edge-disjointness.** If every common vertex of `E₁` and `E₂`
lies in `T`, and no edge of `E₁` has both endpoints in `T`, then `E₁` and `E₂` are disjoint. -/
theorem disjoint_of_vertSet [Fintype V] {E₁ E₂ : Finset (Sym2 V)} (T : Finset V)
    (hT : ∀ x, x ∈ vertSet E₁ → x ∈ vertSet E₂ → x ∈ T)
    (hno : ∀ e ∈ E₁, (∀ x ∈ e, x ∈ T) → False) : Disjoint E₁ E₂ := by
  rw [disjoint_left]
  intro e h₁ h₂
  exact hno e h₁ fun x hx => hT x (mem_vertSet_of_mem h₁ hx) (mem_vertSet_of_mem h₂ hx)

end PartitionedTriangleAbsorption.SignedHinge
