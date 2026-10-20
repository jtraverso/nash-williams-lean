/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Theorem146
import PartitionedTriangleAbsorption.F0OrderedTheorem

/-!
# Theorem 14.6 (branch 12.5 input) from the proved `F₀` theorem

`theorem146Statement_holds : Theorem146Statement` is obtained from the ported, proved
`PartitionedTriangleAbsorption.BlowupB.F0Direct.theorem146_ordered`.

The interfaces are matched literally:

* `partSet p i = partClass p i` (both are `univ.filter (p · = i)`);
* `CloneSupply.partDeg p G i v = NashWilliams18.partDeg G p v i` (filter extensionality, the
  two conjuncts are swapped);
* the "other" label `other0 (p v)` is the label different from `p v`;
* the non-closeness hypothesis is the same proposition: `orderedSideTarget`/`orderedSideCost`
  are, definition by definition, `sideTarget`/`sideCost`, and both sides use the threshold
  `2 * α * |D|²` on ordered pairs (`orderedSideCost = 2 * editDistance` is the content of
  `orderedSideCost_eq_twice_editDistance`, used inside the producer; no factor is dropped here).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma partSet_eq_partClass (p : V → Fin 2) (i : Fin 2) :
    CloneSupply.partSet p i = partClass p i := rfl

omit [DecidableEq V] in
lemma cloneSupply_partDeg_eq (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 2)
    (i : Fin 2) (v : V) : CloneSupply.partDeg p G i v = partDeg G p v i := by
  unfold CloneSupply.partDeg CloneSupply.partNbrs partDeg
  congr 1
  ext w
  simp [and_comm]

lemma other0_ne_self (i : Fin 2) : TypedApplicationLinks.other0 i ≠ i := by
  fin_cases i <;> decide

omit [Fintype V] in
lemma orderedSideCost_eq_sideCost (G : SimpleGraph V) (D X : Finset V) (b : Bool) :
    BlowupB.F0Direct.orderedSideCost G D X b = sideCost G D X b := rfl

/-- **Theorem 14.6, proved.**  The interface `Theorem146Statement` of branch 12.5 holds; it is
the ported `F₀` theorem `theorem146_ordered`. -/
theorem theorem146Statement_holds : Theorem146Statement := by
  intro α hα
  obtain ⟨ε, hε, N, hN⟩ := BlowupB.F0Direct.theorem146_ordered α hα
  refine ⟨ε, hε, N, fun V _ _ p G _ hn hint hid hside => ?_⟩
  obtain ⟨hsize, hint_deg, hcross⟩ := hid
  refine hN V hn p G (fun i => ?_) (fun v => ?_) (fun v => ?_) (fun v => ?_) ?_ hint
  · rw [partSet_eq_partClass]; exact hsize i
  · rw [cloneSupply_partDeg_eq]; exact (hint_deg v).1
  · rw [cloneSupply_partDeg_eq]; exact (hint_deg v).2
  · rw [cloneSupply_partDeg_eq]; exact hcross v _ (other0_ne_self (p v))
  · obtain ⟨i, hi⟩ := hside
    exact ⟨i, by simpa only [IsSideClose, partSet_eq_partClass, orderedSideCost_eq_sideCost] using hi⟩

end NashWilliams18
