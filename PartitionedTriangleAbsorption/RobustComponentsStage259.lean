/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Triangles in the components of a dense graph

This is the component step in robust opposite-edge transport. It works with
Mathlib reachability and does not assume connectedness of the host.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RobustComponentsStage259

open Finset

/-- Above relative minimum degree one third, the presence of a triangle
forces every connected component to contain a triangle. -/
theorem triangle_in_each_component {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdeg : ∀ v, Fintype.card V < 3 * G.degree v)
    (htri : ∃ a b c, G.Adj a b ∧ G.Adj a c ∧ G.Adj b c) (v : V) :
    ∃ a b c, G.Reachable v a ∧ G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  classical
  by_contra hno
  have hvdeg := hdeg v
  change Fintype.card V < 3 * (G.neighborFinset v).card at hvdeg
  have hvpos : 0 < (G.neighborFinset v).card := by omega
  obtain ⟨y, hy⟩ := card_pos.mp hvpos
  have hvy : G.Adj v y := (G.mem_neighborFinset v y).mp hy
  have hxy : Disjoint (G.neighborFinset v) (G.neighborFinset y) := by
    rw [disjoint_left]
    intro w hwv hwy
    exact hno ⟨v, y, w, .refl v, hvy,
      (G.mem_neighborFinset v w).mp hwv, (G.mem_neighborFinset y w).mp hwy⟩
  have hall : ∀ z, G.Reachable v z := by
    intro z
    by_contra hnz
    have hvz : Disjoint (G.neighborFinset v) (G.neighborFinset z) := by
      rw [disjoint_left]
      intro w hwv hwz
      exact hnz (((G.mem_neighborFinset v w).mp hwv).reachable.trans
        ((G.mem_neighborFinset z w).mp hwz).symm.reachable)
    have hyz : Disjoint (G.neighborFinset y) (G.neighborFinset z) := by
      rw [disjoint_left]
      intro w hwy hwz
      exact hnz (hvy.reachable.trans
        (((G.mem_neighborFinset y w).mp hwy).reachable.trans
          ((G.mem_neighborFinset z w).mp hwz).symm.reachable))
    have hc := card_le_univ
      (s := (G.neighborFinset v ∪ G.neighborFinset y) ∪ G.neighborFinset z)
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hvz, hyz⟩),
      card_union_of_disjoint hxy] at hc
    have hydeg := hdeg y
    have hzdeg := hdeg z
    change Fintype.card V < 3 * (G.neighborFinset y).card at hydeg
    change Fintype.card V < 3 * (G.neighborFinset z).card at hzdeg
    omega
  obtain ⟨a, b, c, hab, hac, hbc⟩ := htri
  exact hno ⟨a, b, c, hall a, hab, hac, hbc⟩

end PartitionedTriangleAbsorption.RobustComponentsStage259
