/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.FractionalRepair

@[expose] public section

/-!
# Unconditional padded decomposition for F₁ and F₂

These theorems prove the exact quantified statement supplied with the task,
using the original physical `IsIntDiv`, `triEdges` and `HasDecomp` definitions.
`PaddedInputs` contains the literal supplied padded input definitions because
the current `BlowupB.KeevashPadded` source was not included in the available
October 8 source archive. No absorber, inverse, reserve or repair premise
remains in the results below.
-/

namespace PaddedF12

open PartitionedTriangleAbsorption.TypedApplicationLinks

theorem keevashPaddedSpec_family (kind : Family) :
    PaddedInputs.KeevashPaddedSpec kind.types :=
  keevasPaddedSpec_of_hostRepair kind (hostRepair_F12 kind)

theorem keevashPaddedSpec_F1 : PaddedInputs.KeevashPaddedSpec F1 :=
  keevashPaddedSpec_family .one

theorem keevashPaddedSpec_F2 : PaddedInputs.KeevashPaddedSpec F2 :=
  keevashPaddedSpec_family .two

theorem keevashPaddedSpec_F12 (F : Finset (Multiset (Fin 4)))
    (hF : F = F1 ∨ F = F2) : PaddedInputs.KeevashPaddedSpec F := by
  rcases hF with rfl | rfl
  · exact keevashPaddedSpec_F1
  · exact keevashPaddedSpec_F2

#print axioms hostRepair_F12
#print axioms keevashPaddedSpec_family
#print axioms keevashPaddedSpec_F1
#print axioms keevashPaddedSpec_F2
#print axioms keevashPaddedSpec_F12

end PaddedF12
