/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RobustComponentsStage259
public import PartitionedTriangleAbsorption.OppositeEdgeTransportStage259

/-! # From a triangle in a common link to physical spoke transport

The K5 seed and the component theorem discharge the starting data for the
walk propagation. The triangle-free-link case remains a separate obligation.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.OppositeEdgeTransportStage259

variable {V : Type*} [DecidableEq V]

/-- A triangle in the common link supplies the two initial spokes via a K5. -/
theorem k5_spokes (G : SimpleGraph V) {u v : V} (huv : G.Adj u v)
    {a b c : G.commonNeighbors u v}
    (hab : G.Adj a.val b.val) (hac : G.Adj a.val c.val) (hbc : G.Adj b.val c.val) :
    (oppositeEdgeGraph G).Reachable (edge G huv) (edge G a.property.1) ∧
      (oppositeEdgeGraph G).Reachable (edge G huv) (edge G a.property.2) := by
  have hroot := (opposite_adj G huv hbc b.property.1 c.property.1
    b.property.2 c.property.2).reachable
  constructor
  · exact hroot.trans (opposite_adj G hbc a.property.1 b.property.1.symm
      hab.symm c.property.1.symm hac.symm).reachable
  · exact hroot.trans (opposite_adj G hbc a.property.2 b.property.2.symm
      hab.symm c.property.2.symm hac.symm).reachable

/-- A dense common link containing a triangle connects the root edge to both
spokes at every vertex, even if the common link is disconnected. -/
theorem spokes_of_link_triangle [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v)
    (hdeg : ∀ w : G.commonNeighbors u v,
      Fintype.card (G.commonNeighbors u v) <
        3 * (G.induce (G.commonNeighbors u v)).degree w)
    (htri : ∃ a b c : G.commonNeighbors u v,
      G.Adj a.val b.val ∧ G.Adj a.val c.val ∧ G.Adj b.val c.val)
    (w : G.commonNeighbors u v) :
    (oppositeEdgeGraph G).Reachable (edge G huv) (edge G w.property.1) ∧
      (oppositeEdgeGraph G).Reachable (edge G huv) (edge G w.property.2) := by
  obtain ⟨a, b, c, hwa, hab, hac, hbc⟩ :=
    RobustComponentsStage259.triangle_in_each_component
      (G.induce (G.commonNeighbors u v)) hdeg htri w
  obtain ⟨hu, hv⟩ := k5_spokes G huv hab hac hbc
  exact propagate_spokes G huv hwa.symm (edge G huv) hu hv

end PartitionedTriangleAbsorption.OppositeEdgeTransportStage259
