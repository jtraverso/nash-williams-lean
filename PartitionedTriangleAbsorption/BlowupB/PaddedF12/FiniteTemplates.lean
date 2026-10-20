/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TemplateTransport

@[expose] public section

/-! # Four fixed token templates for F1 and F2

The triangle occupies positions 0,1,2 and has three isolated padding positions.
Every cyclic template is a simple six-cycle on its six distinct positions.
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedDivisibilityCollapse
open PartitionedTriangleAbsorption.TypedRefinerCharge

def triangleSlots : Finset (Sym2 (Fin 6)) := {s(0, 1), s(1, 2), s(2, 0)}

def cycleSlots : Finset (Sym2 (Fin 6)) := {s(0, 1), s(1, 2), s(2, 3), s(3, 4), s(4, 5), s(5, 0)}

def plusLabel : Fin 6 → Fin 4 := ![0, 0, 0, 0, 0, 0]

def minusLabel : Fin 6 → Fin 4 := ![0, 2, 0, 2, 0, 2]

def torsionF1Label : Fin 6 → Fin 4 := ![0, 0, 0, 2, 1, 3]

def torsionF2Label : Fin 6 → Fin 4 := ![0, 0, 0, 2, 1, 2]

theorem triangleSlots_card : triangleSlots.card = 3 := by decide
theorem cycleSlots_card : cycleSlots.card = 6 := by decide

theorem triangleSlots_loopless : ∀ e ∈ triangleSlots, ¬ e.IsDiag := by decide
theorem cycleSlots_loopless : ∀ e ∈ cycleSlots, ¬ e.IsDiag := by decide

theorem triangleSlots_even : ∀ w, Even (incidentLoad triangleSlots w) := by decide
theorem cycleSlots_even : ∀ w, Even (incidentLoad cycleSlots w) := by decide

theorem plus_active_F1 : ActiveEdges F1 plusLabel triangleSlots := by unfold ActiveEdges Link; decide
theorem plus_active_F2 : ActiveEdges F2 plusLabel triangleSlots := by unfold ActiveEdges Link; decide
theorem minus_active_F1 : ActiveEdges F1 minusLabel cycleSlots := by unfold ActiveEdges Link; decide
theorem minus_active_F2 : ActiveEdges F2 minusLabel cycleSlots := by unfold ActiveEdges Link; decide
theorem torsion_active_F1 : ActiveEdges F1 torsionF1Label cycleSlots := by unfold ActiveEdges Link; decide
theorem torsion_active_F2 : ActiveEdges F2 torsionF2Label cycleSlots := by unfold ActiveEdges Link; decide

theorem plus_charge_F1 : charge chi1 plusLabel triangleSlots = 12 := by decide
theorem plus_charge_F2 : charge chi2 plusLabel triangleSlots = 12 := by decide
theorem minus_charge_F1 : charge chi1 minusLabel cycleSlots = -12 := by decide
theorem minus_charge_F2 : charge chi2 minusLabel cycleSlots = -12 := by decide

theorem torsion_freeCharge_F1 : f1FreeCharge torsionF1Label cycleSlots = 0 := by decide
theorem torsion_freeCharge_F2 : f2FreeCharge torsionF2Label cycleSlots = 0 := by decide
theorem torsion_count_F1 : unorderedCount torsionF1Label cycleSlots 0 2 = 1 := by decide
theorem torsion_numerator_F2 : f2Numerator torsionF2Label cycleSlots = 6 := by decide

#print axioms triangleSlots_even
#print axioms cycleSlots_even
#print axioms plus_active_F1
#print axioms plus_active_F2
#print axioms torsion_active_F1
#print axioms torsion_active_F2
#print axioms plus_charge_F1
#print axioms minus_charge_F2
#print axioms torsion_count_F1
#print axioms torsion_numerator_F2

end PaddedF12
