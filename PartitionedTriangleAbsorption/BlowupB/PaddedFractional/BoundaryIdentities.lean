/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# Exact octahedron and prism boundary identities

These hold in every additive commutative group, hence also in the space
of real functions on physical unordered edges. No injectivity is needed
for the identities. Distinct triangle corners and host membership are
separate geometric obligations when applying them to physical triangles.
-/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

variable {V R : Type*} [AddCommGroup R]

def faceBoundary (edge : V → V → R) (a b c : V) : R :=
  edge a b + edge b c + edge c a

theorem octahedron_boundary (edge : V → V → R) (a b c A B C : V) :
    faceBoundary edge a b c =
      faceBoundary edge A b c + faceBoundary edge a B c + faceBoundary edge a b C -
      faceBoundary edge A B c - faceBoundary edge A b C - faceBoundary edge a B C +
      faceBoundary edge A B C := by
  unfold faceBoundary
  abel

theorem prism_boundary (edge : V → V → R) (a b c d A B : V) :
    faceBoundary edge a b c - faceBoundary edge a b d =
      faceBoundary edge a B c + faceBoundary edge A b c + faceBoundary edge A B d -
      faceBoundary edge a B d - faceBoundary edge A b d - faceBoundary edge A B c := by
  unfold faceBoundary
  abel

/-- Coincident third images are allowed: the prism then cancels exactly. -/
theorem prism_coincident_thirds (edge : V → V → R) (a b c A B : V) :
    faceBoundary edge a B c + faceBoundary edge A b c + faceBoundary edge A B c -
      faceBoundary edge a B c - faceBoundary edge A b c - faceBoundary edge A B c = 0 := by
  abel

#print axioms octahedron_boundary
#print axioms prism_boundary
#print axioms prism_coincident_thirds

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
