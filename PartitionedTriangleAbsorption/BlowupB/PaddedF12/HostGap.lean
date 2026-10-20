/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.UniversalF12
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.PaddedBridge

@[expose] public section

/-! # A forbidden class gives a quantitative gap below complete degree -/

namespace PaddedF12

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V] {t D : ℕ}

theorem degree_gap_of_guarded (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (Allowed : Fin t → Fin t → Prop) (ω : ℝ)
    (hG : ∀ u v, G.Adj u v → Allowed (p u) (p v))
    (hforbidden : ∀ i, ∃ j, ¬ Allowed i j)
    (hs : GuardedSupply p G Allowed D (ω * Fintype.card V)) :
    DegBounded G.edgeFinset ((1 - ω) * Fintype.card V) := by
  classical
  intro v
  obtain ⟨j, hj⟩ := hforbidden (p v)
  let C := univ.filter (fun w => p w = j)
  have hdisj : Disjoint (G.neighborFinset v) C := by
    apply disjoint_left.mpr
    intro w hw hC
    have hlabel := (mem_filter.mp hC).2
    exact hj (hlabel ▸ hG v w ((G.mem_neighborFinset v w).mp hw))
  have hcount : (G.neighborFinset v).card + C.card ≤ Fintype.card V := by
    rw [← card_union_of_disjoint hdisj]
    exact card_le_univ _
  have hcountR : ((G.neighborFinset v).card : ℝ) + C.card ≤ Fintype.card V := by
    exact_mod_cast hcount
  have hC : ω * Fintype.card V ≤ (C.card : ℝ) := hs.class_card j
  have hdegree : ((G.neighborFinset v).card : ℝ) ≤ (1 - ω) * Fintype.card V := by
    nlinarith only [hcountR, hC]
  rw [← G.incidenceFinset_eq_filter v, G.card_incidenceFinset_eq_degree]
  exact hdegree

theorem Family.forbidden (kind : Family) (i : Fin 4) :
    ∃ j, ¬ ∃ k, Link kind.types i j k := by
  cases kind <;> fin_cases i <;> simp only [Family.types, Link] <;> decide

theorem Family.host_degree_gap (kind : Family) (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (ω : ℝ)
    (hG : ∀ u v, G.Adj u v → ∃ k, Link kind.types (p u) (p v) k)
    (hs : GuardedSupply p G (fun i j => ∃ k, Link kind.types i j k) D
      (ω * Fintype.card V)) :
    DegBounded G.edgeFinset ((1 - ω) * Fintype.card V) :=
  degree_gap_of_guarded p G _ ω hG kind.forbidden hs

theorem Family.padded_degree_gap (kind : Family) (p : V → Fin 4)
    (J : Finset (Sym2 V)) (hloop : ∀ e ∈ J, ¬ e.IsDiag) (ω : ℝ) (K : ℕ)
    (hK : 1 ≤ K)
    (hallowed : ∀ u v, s(u, v) ∈ J → PaddedInputs.AllowedPair kind.types (p u) (p v))
    (hext : PaddedInputs.ExtendableT K p kind.types J ω) :
    DegBounded J ((1 - ω) * Fintype.card V) := by
  let G := PaddedInputs.edgeGraph J
  have hs := PaddedInputs.guardedSupply_of_padded p kind.types J hloop ω 0 hK hext
  have hG := PaddedInputs.edgeGraph_allowed p kind.types J hallowed
  have hg := kind.host_degree_gap p G ω hG hs
  have hJ : @SimpleGraph.edgeFinset V G G.fintypeEdgeSet = J :=
    @PaddedInputs.edgeGraph_edges V _ J G.fintypeEdgeSet hloop
  simpa only [hJ] using hg

#print axioms degree_gap_of_guarded
#print axioms Family.forbidden
#print axioms Family.padded_degree_gap

end PaddedF12
