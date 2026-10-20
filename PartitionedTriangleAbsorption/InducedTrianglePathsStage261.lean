/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.NonextremalCoreStage260
public import PartitionedTriangleAbsorption.DenseShortPathsStage261
public import PartitionedTriangleAbsorption.RobustComponentsStage259

/-! Bridge the physical finite-set triangle producer to paths in Mathlib's
induced graph. A triangle somewhere is enough: the degree bound forces a
triangle in each component, and the selected path has length at most 14. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.GoodRemaindersStage261

open Finset TriangleFreeCoreStage260

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Finset neighborhood counts agree exactly with induced-graph degrees. -/
theorem induced_degree_eq_filter (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Finset V) (x : (↑J : Set V)) :
    (G.induce (↑J : Set V)).degree x = (J.filter (G.Adj x.val)).card := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  refine card_bij (fun y _ => y.val) ?_ ?_ ?_
  · intro y hy
    exact mem_filter.mpr ⟨y.property,
      ((G.induce (↑J : Set V)).mem_neighborFinset x y).mp hy⟩
  · intro y _ z _ hyz
    exact Subtype.ext hyz
  · intro y hy
    obtain ⟨hyJ, hxy⟩ := mem_filter.mp hy
    exact ⟨⟨y, hyJ⟩, ((G.induce (↑J : Set V)).mem_neighborFinset x ⟨y, hyJ⟩).mpr hxy, rfl⟩

/-- In every component of a large induced remainder, construct a short path
to a physical triangle. All path vertices lie in J by their subtype. -/
theorem induced_short_path_to_triangle (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (J : Finset V) (hJ : 3 * q < 2 * (J.card : ℝ))
    (htri : ∃ x ∈ J, ∃ y ∈ J, ∃ z ∈ J, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z)
    (w : (↑J : Set V)) :
    ∃ a b c : (↑J : Set V), ∃ p : (G.induce (↑J : Set V)).Walk w a,
      p.IsPath ∧ p.length ≤ 14 ∧ G.Adj a.val b.val ∧ G.Adj a.val c.val ∧ G.Adj b.val c.val := by
  classical
  let H := G.induce (↑J : Set V)
  have hcard : Fintype.card (↑J : Set V) = J.card := by simp
  have hdense (x : (↑J : Set V)) : Fintype.card (↑J : Set V) < 3 * H.degree x := by
    have hlower := restricted_degree_lower G q hdeg J x.val
    rw [← induced_degree_eq_filter G J x] at hlower
    have hc : (J.card : ℝ) < 3 * (H.degree x : ℝ) := by
      change (J.card : ℝ) ≤ H.degree x + q at hlower
      linarith
    rw [hcard]
    exact_mod_cast hc
  have htri' : ∃ a b c : (↑J : Set V), H.Adj a b ∧ H.Adj a c ∧ H.Adj b c := by
    obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := htri
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, hxy, hxz, hyz⟩
  obtain ⟨a, b, c, hr, hab, hac, hbc⟩ :=
    RobustComponentsStage259.triangle_in_each_component H hdense htri' w
  obtain ⟨p, hp, hlen⟩ := reachable_walk_le_fourteen H (fun x => by have := hdense x; omega) hr
  exact ⟨a, b, c, p, hp, hlen, hab, hac, hbc⟩

end PartitionedTriangleAbsorption.GoodRemaindersStage261
