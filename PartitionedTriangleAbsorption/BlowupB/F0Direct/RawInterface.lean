/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.Geometry
public import PartitionedTriangleAbsorption.TypedRefinerF0.ChargeF0
public import PartitionedTriangleAbsorption.SignedCertificate.Basic

@[expose] public section

/-!
# The parity-and-edge-count formulation in the request

`pairCount` counts unordered physical edges of the indicated class pair.  Thus
its diagonal entries are exactly the numbers of edges inside the two parts,
and its 01 entry is exactly the number of crossing edges.  The definition
`RawStatement` states the target using graph degrees and these three counts.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks AntiEdgeSelection SignedCertificate
open TypedRefinerCharge TypedRefinerF0

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem incidentLoad_graph_degree (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    incidentLoad G.edgeFinset v = G.degree v := by
  rw [incidentLoad, ← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]

theorem charge_pairCounts (p : V → Fin 2) (E : Finset (Sym2 V)) :
    charge chi0 p E = 2*(pairCount p E 0 1:ℤ)-4*(pairCount p E 0 0:ℤ)-
      4*(pairCount p E 1 1:ℤ) := by
  classical
  have hcount (a b : Fin 2) : (pairCount p E a b:ℤ) =
      ∑ e∈E, if e.map p=s(a,b) then (1:ℤ) else 0 := by
    rw [pairCount,card_filter]
    push_cast
    rfl
  rw [charge_eq_sum,hcount,hcount,hcount,mul_sum,mul_sum,mul_sum,
    ← sum_sub_distrib,← sum_sub_distrib]
  apply sum_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ u v =>
    rw [edge_charge]
    simp only [Sym2.map_mk]
    have hfin (a b : Fin 2) :
        (if a = b then (-4:ℤ) else 2) =
          (2 * if s(a,b) = s(0,1) then (1:ℤ) else 0) -
          (4 * if s(a,b) = s(0,0) then (1:ℤ) else 0) -
          (4 * if s(a,b) = s(1,1) then (1:ℤ) else 0) := by
      fin_cases a <;> fin_cases b <;> norm_num [Sym2.eq_iff]
    exact hfin (p u) (p v)

theorem isIntDiv_of_even_balanced (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj]
    (heven : ∀ v, Even (G.degree v))
    (hbalance : pairCount p G.edgeFinset 0 1 =
      2*(pairCount p G.edgeFinset 0 0+pairCount p G.edgeFinset 1 1)) :
    IsIntDiv p F0 G.edgeFinset := by
  apply isIntDiv_of_charge p
  · intro e he
    exact G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp he)
  · intro v
    rw [incidentLoad_graph_degree]
    exact heven v
  · rw [charge_pairCounts]
    have hb : (pairCount p G.edgeFinset 0 1:ℤ)=
        2*((pairCount p G.edgeFinset 0 0:ℤ)+pairCount p G.edgeFinset 1 1) := by
      exact_mod_cast hbalance
    omega

def RawStatement : Prop :=
  ∀ α : ℝ, 0<α → ∃ ε : ℝ, 0<ε ∧ ∃ N : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V], N≤Fintype.card V →
      ∀ (p : V → Fin 2) (G : SimpleGraph V) [DecidableRel G.Adj],
        HostHyp p G α ε → (∀ v, Even (G.degree v)) →
        pairCount p G.edgeFinset 0 1 =
          2*(pairCount p G.edgeFinset 0 0+pairCount p G.edgeFinset 1 1) →
        HasDecomp p F0 G.edgeFinset

theorem rawStatement_of_statement (h : Statement) : RawStatement := by
  intro α hα
  obtain ⟨ε,hε,N,hN⟩ := h α hα
  refine ⟨ε,hε,N,?_⟩
  intro V _ _ hn p G _ hG he hb
  exact hN V hn p G hG (isIntDiv_of_even_balanced p G he hb)

#print axioms isIntDiv_of_even_balanced
#print axioms rawStatement_of_statement

end PartitionedTriangleAbsorption.BlowupB.F0Direct
