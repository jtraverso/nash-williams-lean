/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateIncidence

@[expose] public section

/-! # Transport of the integral walk interface through a graph equivalence -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

variable {U W : Type*}

theorem fourWalkSupply_equiv (K : SimpleGraph U) (H : SimpleGraph W) (e : U ≃ W)
    (hAdj : ∀ u v, K.Adj u v ↔ H.Adj (e u) (e v))
    (hW : FourWalkSupply H) : FourWalkSupply K := by
  intro u v huv
  obtain ⟨f, h0, h4, hf⟩ := hW (e u) (e v) (fun h => huv (e.injective h))
  refine ⟨fun j => e.symm (f j), ?_, ?_, ?_⟩
  · simp only [h0, Equiv.symm_apply_apply]
  · simp only [h4, Equiv.symm_apply_apply]
  · intro j
    apply (hAdj _ _).mpr
    simpa only [Equiv.apply_symm_apply] using hf j

theorem neighbor_equiv (K : SimpleGraph U) (H : SimpleGraph W) (e : U ≃ W)
    (hAdj : ∀ u v, K.Adj u v ↔ H.Adj (e u) (e v)) (u : U)
    (hN : ∃ w, H.Adj (e u) w) : ∃ v, K.Adj u v := by
  obtain ⟨w, hw⟩ := hN
  refine ⟨e.symm w, (hAdj _ _).mpr ?_⟩
  simpa only [Equiv.apply_symm_apply] using hw

theorem incidenceBasis_of_equiv [DecidableEq U]
    (K : SimpleGraph U) (H : SimpleGraph W) (e : U ≃ W)
    (hAdj : ∀ u v, K.Adj u v ↔ H.Adj (e u) (e v)) (a : U)
    (hW : FourWalkSupply H) (hN : ∃ w, H.Adj (e a) w) :
    Nonempty (IncidenceBasis K a) :=
  incidenceBasis_of_fourWalkSupply K a (fourWalkSupply_equiv K H e hAdj hW)
    (neighbor_equiv K H e hAdj a hN)

#print axioms fourWalkSupply_equiv
#print axioms incidenceBasis_of_equiv

end PartitionedTriangleAbsorption.BlowupB.F0Direct
