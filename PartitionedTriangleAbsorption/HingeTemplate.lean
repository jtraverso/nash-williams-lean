/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Sym.Sym2

/-! A finite six-vertex hinge template. This is not an abundance theorem,
an omniabsorber, or a proof of Theorem 13.16. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.HingeTemplate

abbrev Vertex := Fin 6
abbrev Edge := Sym2 Vertex

def triangle (a b c : Vertex) : Finset Edge := {s(a, b), s(a, c), s(b, c)}

def leftTriangle : Finset Edge := triangle 0 2 4
def rightTriangle : Finset Edge := triangle 0 2 5
def sharedEdge : Edge := s(0, 2)

def hinge : Finset Edge :=
  {s(0, 3), s(0, 5), s(1, 2), s(1, 3), s(1, 4), s(1, 5), s(2, 5),
   s(3, 4), s(3, 5)} \ (leftTriangle ∪ rightTriangle)

def leftParts : Finset (Finset Edge) :=
  {triangle 0 3 4, triangle 1 2 4, triangle 1 3 5}

def rightParts : Finset (Finset Edge) :=
  {triangle 0 3 5, triangle 1 2 5, triangle 1 3 4}

def ExactDecomposition (E : Finset Edge) (Q : Finset (Finset Edge)) : Prop :=
  (∀ t ∈ Q, t.card = 3) ∧
  (Q : Set (Finset Edge)).PairwiseDisjoint id ∧ Q.biUnion id = E

theorem triangles_intersect : leftTriangle ∩ rightTriangle = {sharedEdge} := by decide

theorem hinge_disjoint : Disjoint hinge (leftTriangle ∪ rightTriangle) := by decide

theorem hinge_card : hinge.card = 7 := by decide

theorem left_decomposition :
    ExactDecomposition (hinge ∪ leftTriangle.erase sharedEdge) leftParts := by
  change (∀ t ∈ leftParts, t.card = 3) ∧
    (∀ t ∈ leftParts, ∀ u ∈ leftParts, t ≠ u → Disjoint t u) ∧
    leftParts.biUnion id = hinge ∪ leftTriangle.erase sharedEdge
  decide

theorem right_decomposition :
    ExactDecomposition (hinge ∪ rightTriangle.erase sharedEdge) rightParts := by
  change (∀ t ∈ rightParts, t.card = 3) ∧
    (∀ t ∈ rightParts, ∀ u ∈ rightParts, t ≠ u → Disjoint t u) ∧
    rightParts.biUnion id = hinge ∪ rightTriangle.erase sharedEdge
  decide

/-- Cloning the first two labels preserves the two allowed triangle types. -/
theorem labels_preserved {Label : Type*} (p : Vertex → Label)
    (h01 : p 0 = p 1) (h23 : p 2 = p 3) :
    (p 0, p 3, p 4) = (p 0, p 2, p 4) ∧
    (p 1, p 2, p 4) = (p 0, p 2, p 4) ∧
    (p 1, p 3, p 5) = (p 0, p 2, p 5) ∧
    (p 0, p 3, p 5) = (p 0, p 2, p 5) ∧
    (p 1, p 2, p 5) = (p 0, p 2, p 5) ∧
    (p 1, p 3, p 4) = (p 0, p 2, p 4) := by
  simp only [← h01, ← h23, and_self]

end PartitionedTriangleAbsorption.HingeTemplate
