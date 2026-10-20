/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.RealCoreLinksStage262

/-! Consume an induced short path without replacing its host graph. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoreAssemblyStage262

open Finset GoodRemaindersStage261 OppositeEdgeTransportStage259

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Consume the short path in the exact induced-graph representation
returned by the good-remainder producer. -/
theorem induced_good_path_spoke (G : SimpleGraph V) [DecidableRel G.Adj]
    (a e : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (he : 0 ≤ e)
    (hn : 0 < Fintype.card V) (hsmall : 1000000 * e ≤ a * a)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + (1 / 4 + e) * Fintype.card V)
    (u v s : V) :
    let S := univ.filter (fun t => G.Adj u t ∧ G.Adj v t)
    let B := univ.filter (fun t => t ∉ S ∧ a * Fintype.card V / 100 <
      ((S.filter (fun r => ¬ G.Adj t r)).card : ℝ))
    let R := univ \ (S ∪ B)
    let J := R.filter (G.Adj s)
    ∀ w x y z : (↑J : Set V),
      ∀ p : (G.induce (↑J : Set V)).Walk w x,
        p.length ≤ 14 → G.Adj x.val y.val → G.Adj x.val z.val →
        ∀ hyz : G.Adj y.val z.val,
          (oppositeEdgeGraph G).Reachable
            (edge G (mem_filter.mp w.property).2) (edge G hyz) := by
  classical
  intro S B R J w x y z p hlen hxy hxz hyz
  let Q := p.map (SimpleGraph.Embedding.induce (G := G) (↑J : Set V)).toHom
  have hlength : Q.length ≤ 14 := by
    simpa only [Q, SimpleGraph.Walk.length_map] using hlen
  have hsupport : ∀ t ∈ Q.support, t ∈ R ∧ G.Adj s t := by
    intro t ht
    rw [SimpleGraph.Walk.support_map] at ht
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp ht
    exact mem_filter.mp r.property
  exact good_path_spoke_reaches_triangle G a e ha ha1 he hn hsmall hdeg u v s
    w.val x.val y.val z.val (mem_filter.mp w.property).2 Q hlength hxy hxz hyz
    hsupport (mem_filter.mp y.property) (mem_filter.mp z.property)

end PartitionedTriangleAbsorption.CoreAssemblyStage262
