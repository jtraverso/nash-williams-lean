/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.F0OrderedBridge
import PartitionedTriangleAbsorption.BlowupB.F0Direct.Theorem146

/-! The proved F₀ theorem with the ordered-pair non-extremality convention.
This is a local 4.35 interface, not an import of the independent NW 4.28 project. -/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply TypedApplicationLinks

theorem theorem146_ordered :
    ∀ α : ℝ, 0 < α → ∃ ε : ℝ, 0 < ε ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
        ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
          (∀ i, (1 - ε) * Fintype.card V / 2 ≤ ((partSet p i).card : ℝ)) →
          (∀ v, (1 / 4 - ε) * Fintype.card V ≤ (partDeg p G (p v) v : ℝ)) →
          (∀ v, (partDeg p G (p v) v : ℝ) ≤ (1 / 4 + ε) * Fintype.card V) →
          (∀ v, (1 / 2 - ε) * Fintype.card V ≤ (partDeg p G (other0 (p v)) v : ℝ)) →
          (∃ i, ¬ ∃ X ⊆ partSet p i, X.card = (partSet p i).card / 2 ∧
            ∃ b : Bool, (orderedSideCost G (partSet p i) X b : ℝ) ≤
              2 * α * ((partSet p i).card : ℝ)^2) →
          IsIntDiv p F0 G.edgeFinset → HasDecomp p F0 G.edgeFinset := by
  intro α hα
  obtain ⟨ε, hε, N, hN⟩ := statement α hα
  refine ⟨ε, hε, N, ?_⟩
  intro V _ _ hn p G _ hsize hlo hhi hcross hgood hdiv
  apply hN V hn p G _ hdiv
  refine ⟨hsize, hlo, hhi, hcross, ?_⟩
  obtain ⟨i, hi⟩ := hgood
  exact ⟨i, (nonextreme_iff_not_orderedClose G (partSet p i) α).mpr hi⟩

#print axioms theorem146_ordered

end PartitionedTriangleAbsorption.BlowupB.F0Direct
