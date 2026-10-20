/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedTransportExamples

/-! # Exact piece conditions for F0--F3

For each of the four fixed families, a loopless edge set is integrally divisible exactly when
it uses only active pairs, has even vertex degrees, and its global edge-type vector is an
integer combination of the type edge vectors. This is the precise local check a refiner piece
(or a leftover) must pass; the global coefficient condition is the only non-local part.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedPieceConditions

open Finset TypedApplicationLinks TypedTransformer TypedDivisibilityCollapse AntiEdgeSelection
  TypedTransportExamples

variable {V : Type*} [DecidableEq V]

theorem F0_isIntDiv_iff {p : V → Fin 2} {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F0 E ↔ ActiveEdges F0 p E ∧ (∀ v, Even (incidentLoad E v)) ∧
      ∃ c : Multiset (Fin 2) → ℤ, edgeVec p E = ∑ τ ∈ F0, c τ • typeEdgeVec τ :=
  isIntDiv_iff F0_three_step F0_card hloop

theorem F1_isIntDiv_iff {p : V → Fin 4} {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F1 E ↔ ActiveEdges F1 p E ∧ (∀ v, Even (incidentLoad E v)) ∧
      ∃ c : Multiset (Fin 4) → ℤ, edgeVec p E = ∑ τ ∈ F1, c τ • typeEdgeVec τ :=
  isIntDiv_iff F1_three_step F1_card hloop

theorem F2_isIntDiv_iff {p : V → Fin 4} {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F2 E ↔ ActiveEdges F2 p E ∧ (∀ v, Even (incidentLoad E v)) ∧
      ∃ c : Multiset (Fin 4) → ℤ, edgeVec p E = ∑ τ ∈ F2, c τ • typeEdgeVec τ :=
  isIntDiv_iff F2_three_step F2_card hloop

theorem F3_isIntDiv_iff {p : V → Fin 4} {E : Finset (Sym2 V)} (hloop : ∀ e ∈ E, ¬ e.IsDiag) :
    IsIntDiv p F3 E ↔ ActiveEdges F3 p E ∧ (∀ v, Even (incidentLoad E v)) ∧
      ∃ c : Multiset (Fin 4) → ℤ, edgeVec p E = ∑ τ ∈ F3, c τ • typeEdgeVec τ :=
  isIntDiv_iff F3_three_step F3_card hloop

end PartitionedTriangleAbsorption.TypedPieceConditions
