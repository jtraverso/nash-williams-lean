/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingRestriction
public import Mathlib.Tactic.NormNum

/-! # The classical K5 edge gadget, scaled by six

The finite identity is kernel-checked. This does not prove that an arbitrary
host has enough allowed K5 copies, nor apply it silently to restricted types.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.K5EdgeGadget

open Finset

abbrev Vertex := Fin 5

def triangles : Finset (Finset Vertex) := univ.powersetCard 3

def coefficient (T : Finset Vertex) : ℤ :=
  if (T ∩ {0, 1}).card = 1 then -1 else 2

/-- Six times the local gadget has edge mass six at 01 and zero elsewhere. -/
theorem incidence_identity : ∀ u v : Vertex, u ≠ v →
    (∑ T ∈ triangles with s(u, v) ∈ triEdges T, coefficient T) =
      if s(u, v) = s(0, 1) then 6 else 0 := by decide

theorem triangles_card : triangles.card = 10 := by decide

theorem positive_count : (triangles.filter (fun T => coefficient T = 2)).card = 4 := by
  decide

theorem negative_count : (triangles.filter (fun T => coefficient T = -1)).card = 6 := by
  decide

theorem coefficient_bounds (T : Finset Vertex) : -1 ≤ coefficient T ∧ coefficient T ≤ 2 := by
  unfold coefficient
  split_ifs <;> norm_num

end PartitionedTriangleAbsorption.K5EdgeGadget
