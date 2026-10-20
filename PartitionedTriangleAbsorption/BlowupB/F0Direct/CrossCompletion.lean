/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.GeometryBounds

/-! # Completing only the crossing edges -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.CrossCompletion

variable {V : Type*}

def complete (p : V → Fin 2) (J : SimpleGraph V) : SimpleGraph V where
  Adj u v := J.Adj u v ∨ p u ≠ p v
  symm := by
    constructor
    intro u v h
    exact h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)
  loopless := ⟨fun _ h => h.elim (fun h => h.ne rfl) (fun h => h rfl)⟩

instance (p : V → Fin 2) (J : SimpleGraph V) [DecidableRel J.Adj] :
    DecidableRel (complete p J).Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

@[simp] theorem complete_adj (p : V → Fin 2) (J : SimpleGraph V) (u v : V) :
    (complete p J).Adj u v ↔ J.Adj u v ∨ p u ≠ p v := Iff.rfl

theorem le_complete (p : V → Fin 2) (J : SimpleGraph V) : J ≤ complete p J :=
  fun _ _ h => Or.inl h

theorem internal (p : V → Fin 2) (J : SimpleGraph V) (u v : V) (h : p u = p v) :
    (complete p J).Adj u v ↔ J.Adj u v := by simp [h]

#print axioms le_complete
#print axioms internal

end PartitionedTriangleAbsorption.BlowupB.F0Direct.CrossCompletion
