/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CoordinateTransport
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RealCompleteSumCoordinates
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateCrossMatrix
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CrossCompletion

@[expose] public section

/-! # Physical coordinates on the crossing completion of the given partition -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.HostRealCoordinates

open Finset TypedApplicationLinks
open PartitionedTriangleAbsorption.F0Direct.RealComplete

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev partGraph (p : V → Fin 2) (G : SimpleGraph V) (i : Fin 2) :
    SimpleGraph (PartVertex p i) := G.comap Subtype.val

def splitEquiv (p : V → Fin 2) (i : Fin 2) :
    PartVertex p i ⊕ PartVertex p (other0 i) ≃ V where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun v := if h : p v = i then Sum.inl ⟨v,h⟩ else
    Sum.inr ⟨v,(eq_or_eq_other0 i (p v)).resolve_left h⟩
  left_inv x := by
    rcases x with a | b
    · simp [a.property]
    · simp [b.property, other0_ne i]
  right_inv v := by
    dsimp
    split_ifs <;> rfl

@[simp] theorem splitEquiv_inl (p : V → Fin 2) (i : Fin 2) (a : PartVertex p i) :
    splitEquiv p i (Sum.inl a) = a.val := rfl

@[simp] theorem splitEquiv_inr (p : V → Fin 2) (i : Fin 2)
    (b : PartVertex p (other0 i)) : splitEquiv p i (Sum.inr b) = b.val := rfl

theorem split_adj (p : V → Fin 2) (G : SimpleGraph V) (i : Fin 2)
    (u v : PartVertex p i ⊕ PartVertex p (other0 i)) :
    (SumModel.joined (partGraph p G i) (partGraph p G (other0 i))).Adj u v ↔
      (CrossCompletion.complete p G).Adj (splitEquiv p i u) (splitEquiv p i v) := by
  rcases u with a | b <;> rcases v with a' | b'
  · change G.Adj a.val a'.val ↔ G.Adj a.val a'.val ∨ p a.val ≠ p a'.val
    simp [a.property, a'.property]
  · change True ↔ G.Adj a.val b'.val ∨ p a.val ≠ p b'.val
    simp [a.property, b'.property, (other0_ne i).symm]
  · change True ↔ G.Adj b.val a'.val ∨ p b.val ≠ p a'.val
    simp [b.property, a'.property, other0_ne i]
  · change G.Adj b.val b'.val ↔ G.Adj b.val b'.val ∨ p b.val ≠ p b'.val
    simp [b.property, b'.property]

theorem split_part (p : V → Fin 2) (i : Fin 2)
    (u v : PartVertex p i ⊕ PartVertex p (other0 i)) :
    SumModel.part u = SumModel.part v ↔ p (splitEquiv p i u) = p (splitEquiv p i v) := by
  rcases u with a | b <;> rcases v with a' | b'
  · simp [SumModel.part, a.property, a'.property]
  · simp [SumModel.part, a.property, b'.property, (other0_ne i).symm]
  · simp [SumModel.part, b.property, a'.property, other0_ne i]
  · simp [SumModel.part, b.property, b'.property]

noncomputable def coordinates (p : V → Fin 2) (G : SimpleGraph V)
    [DecidableRel G.Adj] (i : Fin 2) :
    Coordinates p (CrossCompletion.complete p G)
      (Internal.matrix (partGraph p G i)) (Internal.matrix (partGraph p G (other0 i))) :=
  CoordinateTransport.coordinates SumModel.part p
    (SumModel.joined (partGraph p G i) (partGraph p G (other0 i)))
    (CrossCompletion.complete p G) _ _
    (SumModel.coordinates (partGraph p G i) (partGraph p G (other0 i)))
    (splitEquiv p i) (split_adj p G i) (split_part p i)

#print axioms coordinates

end PartitionedTriangleAbsorption.BlowupB.F0Direct.HostRealCoordinates
