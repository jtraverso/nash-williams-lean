/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedF12.ExplicitTerminal
import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.GuardedLedger

/-!
# The numerical F1/F2 terminal step in the private-family ledger
-/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.StructuralF3General.PrivateFamily

/-- The private terminal step has the fixed 144-edge input and `2^21` output budgets. -/
theorem guarded_privateStep_F12 (F : Finset (Multiset (Fin 4))) (hF : F = F1 ∨ F = F2)
    {V : Type*} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (a T D : ℝ)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) a)
    (hD0 : 0 ≤ D) (hT : 0 < T)
    (hbudget : (2 ^ 21 : ℝ) + (2 ^ 21 : ℝ) * D < a / 2) :
    PrivateStep p F G 144 (2 ^ 21) T D a := by
  intro L hL hLc P hPG hm hdiv
  classical
  let High : Finset V := univ.filter fun v => T < (incidentLoad L v : ℝ)
  have hHigh : (High.card : ℝ) ≤ a / 2 := by
    have hc := card_highLoad_le L T
    change (High.card : ℝ) * T ≤ 2 * L.card at hc
    nlinarith
  have hbudget' : (2 ^ 21 : ℝ) + High.card + (2 ^ 21 : ℝ) * D < a := by
    linarith
  have hloop : ∀ e ∈ P, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      have hxy : G.Adj x y := SimpleGraph.mem_edgeFinset.mp (hPG he)
      intro hd
      exact G.ne_of_adj hxy (by simpa using hd)
  obtain ⟨A, hA⟩ := guarded_terminal_F12 F hF p G a D L High hs hL hD0 hbudget' P hm hloop hdiv
  refine ⟨A, hA.subgraph, hA.avoidLedger, hA.decomp, hA.decomp_union, hA.card_le, ?_⟩
  intro v hv
  rcases hA.vertices v hv with hp | hz
  · exact Or.inl hp
  · exact Or.inr (le_of_not_gt fun h => hz (mem_filter.mpr ⟨mem_univ _, h⟩))

#print axioms guarded_privateStep_F12

end PaddedF12
