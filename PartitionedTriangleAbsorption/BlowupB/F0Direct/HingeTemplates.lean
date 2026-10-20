/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PhysicalHingeSupply.Template
public import PartitionedTriangleAbsorption.TypedApplicationLinks

/-! # Three finite physical F0 hinge templates

The long templates use only one internal edge in the part whose expansion is
unknown, and a path of length three or four in the good part.  Every assertion
below concerns exact finite edge sets and positive, pairwise edge-disjoint
triangle decompositions.  No host abundance statement is assumed here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HingeTemplates

open Finset TypedApplicationLinks PhysicalHingeSupply

namespace Good

/-! Vertices: `0=u, 1=v, 2=x, 3=y, 4=s, 5=t`. -/

def firstRoot : Finset (Fin 6) := {0, 1, 2}
def secondRoot : Finset (Fin 6) := {0, 1, 3}

def edges : Finset (Sym2 (Fin 6)) :=
  {s(0, 4), s(4, 5), s(5, 1), s(4, 2), s(4, 3), s(5, 2), s(5, 3)}

def positive : Finset (Finset (Fin 6)) :=
  {{0, 4, 2}, {4, 5, 3}, {5, 1, 2}}

def negative : Finset (Finset (Fin 6)) :=
  {{0, 4, 3}, {4, 5, 2}, {5, 1, 3}}

def part (a : Fin 2) : Fin 6 → Fin 2 :=
  ![a, a, other0 a, other0 a, a, a]

theorem edges_card : edges.card = 7 := by decide

theorem support : vertSet edges = univ := by
  unfold vertSet edges
  decide

theorem disjoint_roots : Disjoint edges (triEdges firstRoot ∪ triEdges secondRoot) := by
  unfold edges triEdges firstRoot secondRoot
  decide

theorem positive_edges :
    positive.biUnion triEdges = edges ∪ (triEdges firstRoot \ triEdges secondRoot) := by
  unfold positive edges triEdges firstRoot secondRoot
  decide

theorem negative_edges :
    negative.biUnion triEdges = edges ∪ (triEdges secondRoot \ triEdges firstRoot) := by
  unfold negative edges triEdges firstRoot secondRoot
  decide

theorem positive_disjoint :
    (positive : Set (Finset (Fin 6))).PairwiseDisjoint triEdges := by
  intro a ha b hb hab
  simp only [positive, coe_insert, coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)

theorem negative_disjoint :
    (negative : Set (Finset (Fin 6))).PairwiseDisjoint triEdges := by
  intro a ha b hb hab
  simp only [negative, coe_insert, coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)

theorem positive_typed (a : Fin 2) : ∀ s ∈ positive, IsTypedTri (part a) F0 s := by
  intro s hs
  simp only [positive, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;> fin_cases a <;> unfold IsTypedTri <;> decide

theorem negative_typed (a : Fin 2) : ∀ s ∈ negative, IsTypedTri (part a) F0 s := by
  intro s hs
  simp only [negative, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;> fin_cases a <;> unfold IsTypedTri <;> decide

theorem hinge (a : Fin 2) : IsHinge (part a) F0 firstRoot secondRoot edges := by
  exact ⟨disjoint_roots,
    ⟨positive, positive_typed a, positive_disjoint, positive_edges⟩,
    ⟨negative, negative_typed a, negative_disjoint, negative_edges⟩⟩

theorem mapped_hinge {V : Type*} [DecidableEq V] (p : V → Fin 2)
    (f : Fin 6 ↪ V) (a : Fin 2) (hp : ∀ i, p (f i) = part a i) :
    IsHinge p F0 (firstRoot.map f) (secondRoot.map f) (edges.map (edgeEmb f)) :=
  isHinge_map f hp (hinge a)

end Good

namespace Bad

/-! Vertices: `0=u, 1=v, 2=x, 3=y, 4=q, 5=r1, 6=r2, 7=r3`. -/

def firstRoot : Finset (Fin 8) := {0, 1, 2}
def secondRoot : Finset (Fin 8) := {0, 1, 3}

def edges : Finset (Sym2 (Fin 8)) :=
  {s(0, 4), s(4, 2), s(4, 3), s(2, 5), s(5, 6), s(6, 7), s(7, 3),
   s(4, 5), s(4, 6), s(4, 7), s(1, 5), s(1, 6), s(1, 7)}

def positive : Finset (Finset (Fin 8)) :=
  {{0, 4, 2}, {1, 2, 5}, {4, 5, 6}, {1, 6, 7}, {4, 7, 3}}

def negative : Finset (Finset (Fin 8)) :=
  {{0, 4, 3}, {4, 2, 5}, {1, 5, 6}, {4, 6, 7}, {1, 7, 3}}

def part (a : Fin 2) : Fin 8 → Fin 2 :=
  ![a, a, other0 a, other0 a, a, other0 a, other0 a, other0 a]

theorem edges_card : edges.card = 13 := by decide

theorem support : vertSet edges = univ := by
  unfold vertSet edges
  decide

theorem disjoint_roots : Disjoint edges (triEdges firstRoot ∪ triEdges secondRoot) := by
  unfold edges triEdges firstRoot secondRoot
  decide

theorem positive_edges :
    positive.biUnion triEdges = edges ∪ (triEdges firstRoot \ triEdges secondRoot) := by
  unfold positive edges triEdges firstRoot secondRoot
  decide

theorem negative_edges :
    negative.biUnion triEdges = edges ∪ (triEdges secondRoot \ triEdges firstRoot) := by
  unfold negative edges triEdges firstRoot secondRoot
  decide

theorem positive_disjoint :
    (positive : Set (Finset (Fin 8))).PairwiseDisjoint triEdges := by
  intro a ha b hb hab
  simp only [positive, coe_insert, coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)

theorem negative_disjoint :
    (negative : Set (Finset (Fin 8))).PairwiseDisjoint triEdges := by
  intro a ha b hb hab
  simp only [negative, coe_insert, coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl | rfl | rfl <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)

theorem positive_typed (a : Fin 2) : ∀ s ∈ positive, IsTypedTri (part a) F0 s := by
  intro s hs
  simp only [positive, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> fin_cases a <;> unfold IsTypedTri <;> decide

theorem negative_typed (a : Fin 2) : ∀ s ∈ negative, IsTypedTri (part a) F0 s := by
  intro s hs
  simp only [negative, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl <;> fin_cases a <;> unfold IsTypedTri <;> decide

theorem hinge (a : Fin 2) : IsHinge (part a) F0 firstRoot secondRoot edges := by
  exact ⟨disjoint_roots,
    ⟨positive, positive_typed a, positive_disjoint, positive_edges⟩,
    ⟨negative, negative_typed a, negative_disjoint, negative_edges⟩⟩

theorem mapped_hinge {V : Type*} [DecidableEq V] (p : V → Fin 2)
    (f : Fin 8 ↪ V) (a : Fin 2) (hp : ∀ i, p (f i) = part a i) :
    IsHinge p F0 (firstRoot.map f) (secondRoot.map f) (edges.map (edgeEmb f)) :=
  isHinge_map f hp (hinge a)

end Bad

namespace Cross

/-! The four values of `k` encode the parts of the two third vertices:
`(a,a)`, `(other a,other a)`, `(a,other a)`, `(other a,a)`. -/

def part (a : Fin 2) (k : Fin 4) : Fin 6 → Fin 2 :=
  ![![a, other0 a, a, a, other0 a, other0 a],
    ![a, other0 a, other0 a, other0 a, a, a],
    ![a, other0 a, a, other0 a, a, other0 a],
    ![a, other0 a, other0 a, a, a, other0 a]] k

theorem support : vertSet tmplH = univ := by
  unfold vertSet tmplH
  decide

theorem positive_typed (a : Fin 2) (k : Fin 4) :
    ∀ s ∈ modeD, IsTypedTri (part a k) F0 s := by
  intro s hs
  simp only [modeD, mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;> fin_cases a <;> fin_cases k <;> unfold IsTypedTri <;> decide

theorem negative_typed (a : Fin 2) (k : Fin 4) :
    ∀ s ∈ modeD', IsTypedTri (part a k) F0 s := by
  intro s hs
  simp only [modeD', mem_insert, mem_singleton] at hs
  rcases hs with rfl | rfl | rfl <;> fin_cases a <;> fin_cases k <;> unfold IsTypedTri <;> decide

theorem hinge (a : Fin 2) (k : Fin 4) : IsHinge (part a k) F0 rootS rootS' tmplH := by
  exact ⟨tmpl_disjoint,
    ⟨modeD, positive_typed a k, tmpl_first_disjoint, tmpl_first_edges⟩,
    ⟨modeD', negative_typed a k, tmpl_second_disjoint, tmpl_second_edges⟩⟩

theorem mapped_hinge {V : Type*} [DecidableEq V] (p : V → Fin 2)
    (f : Fin 6 ↪ V) (a : Fin 2) (k : Fin 4) (hp : ∀ i, p (f i) = part a k i) :
    IsHinge p F0 (rootS.map f) (rootS'.map f) (tmplH.map (edgeEmb f)) :=
  isHinge_map f hp (hinge a k)

end Cross

#print axioms Good.hinge
#print axioms Bad.hinge
#print axioms Cross.hinge
#print axioms Good.mapped_hinge
#print axioms Bad.mapped_hinge
#print axioms Cross.mapped_hinge

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HingeTemplates
