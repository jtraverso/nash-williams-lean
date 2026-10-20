/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AntiEdgeSelection

/-! # Finite controls: the exclusion budget must be strict

In the complete graph on seven vertices, roots 0 and 1 have five candidates.
Four blocked root edges and one excluded vertex remove every candidate.
Freeing one blocked edge restores exactly one candidate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.AntiEdgeSelection.Controls

def candidates : Finset (Fin 7) := {2, 3, 4, 5, 6}
def excluded : Finset (Fin 7) := {6}
def blocked : Finset (Sym2 (Fin 7)) := {s(0, 2), s(0, 3), s(1, 4), s(1, 5)}
def repaired : Finset (Sym2 (Fin 7)) := {s(0, 2), s(0, 3), s(1, 4)}

theorem physical_candidates :
    candidates = Finset.univ.filter (fun w =>
      (⊤ : SimpleGraph (Fin 7)).Adj 0 w ∧ (⊤ : SimpleGraph (Fin 7)).Adj w 1) := by
  decide

theorem equality_budget :
    excluded.card + incidentLoad blocked 0 + incidentLoad blocked 1 = candidates.card := by
  decide

theorem no_available_at_equality :
    candidates \ (excluded ∪ blockedNeighbours blocked 0 ∪ blockedNeighbours blocked 1) = ∅ := by
  decide

theorem repaired_budget :
    excluded.card + incidentLoad repaired 0 + incidentLoad repaired 1 < candidates.card := by
  decide

theorem repaired_available :
    candidates \ (excluded ∪ blockedNeighbours repaired 0 ∪
      blockedNeighbours repaired 1) = {5} := by
  decide

end PartitionedTriangleAbsorption.AntiEdgeSelection.Controls
