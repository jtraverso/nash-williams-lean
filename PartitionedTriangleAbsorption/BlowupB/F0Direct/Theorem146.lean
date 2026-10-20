/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.WeightProducer
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.RawInterface

@[expose] public section

/-!
# The F0 decomposition theorem for the nonextreme two-part branch

The theorem `theorem146` has precisely the parity, edge-balance and geometric
hypotheses of the request, expressed by `RawStatement`.  Both geometric
producers in the global absorption consumer are discharged here.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks

theorem producers (a : ℝ) (ha : 0<a) :
    ∃ N : ℕ, LocalTerminal.{0} a (localEpsilon a) N 214 (terminalCost 214) ∧
      WeightProducer a (localEpsilon a) N := by
  obtain ⟨Nt,ht⟩ := terminal_producer.{0} a ha
  obtain ⟨Nw,hw⟩ := weight_producer a ha
  refine ⟨Nt+Nw,?_,?_⟩
  · intro V _ _ hn p G _ hG P hPG hPm hPdiv
    exact ht V (by omega) p G hG P hPG hPm hPdiv
  · intro V _ _ hn p G _ hG hdiv
    exact hw V (by omega) p G hG hdiv

/-- Exact mixed-triangle decomposition with integral divisibility. -/
theorem statement : Statement := by
  intro α hα
  have ha : 0<α/2 := by positivity
  obtain ⟨N0,ht,hw⟩ := producers (α/2) ha
  obtain ⟨ε,he,N,hN⟩ := decomposition_from_producers (α/2) (localEpsilon (α/2))
    ha (localEpsilon_pos ha) N0 (terminalCost 214) (by norm_num [terminalCost]) ht hw
  refine ⟨ε,he,N,?_⟩
  intro V _ _ hn p G _ hG hdiv
  exact hN V hn p G (by convert hG using 1 <;> ring) hdiv

/-- The parity-and-balance statement requested for branch 12.5. -/
theorem theorem146 : RawStatement := rawStatement_of_statement statement

#print axioms producers
#print axioms statement
#print axioms theorem146

end PartitionedTriangleAbsorption.BlowupB.F0Direct
