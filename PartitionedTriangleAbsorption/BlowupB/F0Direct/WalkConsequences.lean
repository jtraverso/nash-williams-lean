/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkCounts
import PartitionedTriangleAbsorption.BlowupB.F0Direct.SignlessSupport
import PartitionedTriangleAbsorption.BlowupB.F0Direct.CertificateIncidence
import Mathlib.Tactic.FinCases

/-!
# From diagonal walk counts to a supported incidence inverse

The diagonal count of ordered length-three walks in the internal part is
exactly the count of ordered opposite pairs used by the physical signless
inverse.  These are identities of finite counts, with no asymptotic step.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkConsequences

open Finset WalkSupply
open PartitionedTriangleAbsorption.F0Direct.SignlessTriangle

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A positive ordered edge count between the two neighborhoods gives an
actual three-edge walk with both internal vertices in the prescribed part. -/
theorem threeWalk_exists_of_arcs_pos
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (u v : V)
    (h : 0 < arcs G (neighbors G D u) (neighbors G D v)) :
    ∃ a ∈ D, ∃ b ∈ D, G.Adj u a ∧ G.Adj a b ∧ G.Adj b v := by
  classical
  rw [arcs_eq_card_pairs] at h
  have hc : 0 < ((neighbors G D u ×ˢ neighbors G D v).filter
      fun ab => G.Adj ab.1 ab.2).card := by exact_mod_cast h
  obtain ⟨⟨a, b⟩, hab⟩ := Finset.card_pos.mp hc
  obtain ⟨hpair, hadj⟩ := mem_filter.mp hab
  obtain ⟨ha, hb⟩ := mem_product.mp hpair
  obtain ⟨haD, hua⟩ := (mem_neighbors G D u a).mp ha
  obtain ⟨hbD, hvb⟩ := (mem_neighbors G D v b).mp hb
  exact ⟨a, haD, b, hbD, hua, hadj, hvb.symm⟩

/-- Positivity for every pair gives the even-walk interface used by the
integral certificate construction.  Repeated vertices in a walk are allowed. -/
theorem fourWalkSupply_of_arcs_pos
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (hwalk : ∀ u ∈ D, ∀ v ∈ D,
      0 < arcs G (neighbors G D u) (neighbors G D v)) :
    FourWalkSupply (G.induce (D : Set V)) := by
  classical
  intro u v _
  obtain ⟨c, hcD, _, _, huc, _, _⟩ :=
    threeWalk_exists_of_arcs_pos G D u u (hwalk u u.property u u.property)
  obtain ⟨a, haD, b, hbD, hca, hab, hbv⟩ :=
    threeWalk_exists_of_arcs_pos G D c v (hwalk c hcD v v.property)
  let c' : (D : Set V) := ⟨c, hcD⟩
  let a' : (D : Set V) := ⟨a, haD⟩
  let b' : (D : Set V) := ⟨b, hbD⟩
  refine ⟨![u, c', a', b', v], rfl, rfl, ?_⟩
  intro j
  fin_cases j
  · exact huc
  · exact hca
  · exact hab
  · exact hbv

theorem neighbor_in_induced_of_arcs_pos
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (u : (D : Set V))
    (h : 0 < arcs G (neighbors G D u) (neighbors G D u)) :
    ∃ v : (D : Set V), (G.induce (D : Set V)).Adj u v := by
  obtain ⟨v, hvD, _, _, huv, _, _⟩ := threeWalk_exists_of_arcs_pos G D u u h
  exact ⟨⟨v, hvD⟩, huv⟩

/-- The same walk input therefore provides the bounded integral incidence
basis required for signed certificates, for any chosen anchor. -/
theorem incidenceBasis_of_arcs_pos
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (hwalk : ∀ u ∈ D, ∀ v ∈ D,
      0 < arcs G (neighbors G D u) (neighbors G D v))
    (a : (D : Set V)) : Nonempty (IncidenceBasis (G.induce (D : Set V)) a) :=
  incidenceBasis_of_fourWalkSupply _ a (fourWalkSupply_of_arcs_pos G D hwalk)
    (neighbor_in_induced_of_arcs_pos G D a (hwalk a a.property a a.property))

theorem arcs_neighbors_self_eq_trianglePairs
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V) (u : (D : Set V)) :
    arcs G (neighbors G D u) (neighbors G D u) =
      ((trianglePairs (G.induce (D : Set V)) u).card : ℝ) := by
  classical
  have hs (f : V → ℝ) : (∑ a : (D : Set V), f a) = ∑ a ∈ D, f a :=
    (Finset.sum_subtype D (fun _ => Iff.rfl) f).symm
  calc
    _ = ∑ a ∈ D, ∑ b ∈ D,
        if G.Adj u a ∧ G.Adj u b ∧ G.Adj a b then (1 : ℝ) else 0 := by
      rw [arcs_eq_sum]
      simp only [neighbors, Finset.sum_filter, ite_and, Finset.sum_ite_irrel,
        Finset.sum_const_zero]
    _ = ∑ a : (D : Set V), ∑ b : (D : Set V),
        if G.Adj u a ∧ G.Adj u b ∧ G.Adj a b then (1 : ℝ) else 0 := by
      symm
      calc
        _ = ∑ a ∈ D, ∑ b : (D : Set V),
            if G.Adj u a ∧ G.Adj u b ∧ G.Adj a b then (1 : ℝ) else 0 :=
          hs (fun a => ∑ b : (D : Set V),
            if G.Adj u a ∧ G.Adj u b ∧ G.Adj a b then (1 : ℝ) else 0)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro a _
          exact hs (fun b =>
            if G.Adj u a ∧ G.Adj u b ∧ G.Adj a b then (1 : ℝ) else 0)
    _ = _ := by
      simp only [trianglePairs, card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero, Fintype.sum_prod_type, SimpleGraph.induce_adj]

/-- Uniform positive diagonal walk counts give an actual supported right
inverse for the internal graph.  The lower bound is for ordered pairs. -/
theorem incidence_inverse_of_diagonal_walks
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset V)
    (d : ℝ) (hd : 0 < d)
    (hwalk : ∀ u ∈ D, d ≤ arcs G (neighbors G D u) (neighbors G D u)) :
    (∀ x, incidence (G.induce (D : Set V))
      (triangleInverse (G.induce (D : Set V)) x) = x) ∧
    (∀ x e, e ∉ (G.induce (D : Set V)).edgeSet →
      triangleInverse (G.induce (D : Set V)) x e = 0) ∧
    (∀ (x : ↥(D : Set V) → ℝ) (M : ℝ), 0 ≤ M → (∀ u, |x u| ≤ M) →
      ∀ e, |triangleInverse (G.induce (D : Set V)) x e| ≤
        3 * (D.card : ℝ) * M / d) := by
  classical
  have hcount (u : (D : Set V)) :
      d ≤ ((trianglePairs (G.induce (D : Set V)) u).card : ℝ) := by
    rw [← arcs_neighbors_self_eq_trianglePairs G D u]
    exact hwalk u u.property
  have hpos (u : (D : Set V)) : 0 < (trianglePairs (G.induce (D : Set V)) u).card := by
    have : (0 : ℝ) < ((trianglePairs (G.induce (D : Set V)) u).card : ℝ) :=
      lt_of_lt_of_le hd (hcount u)
    exact_mod_cast this
  refine ⟨incidence_triangleInverse _ hpos, ?_, ?_⟩
  · intro x e he
    exact triangleInverse_eq_zero_of_not_mem _ x he
  · intro x M hM hx e
    have hcard : Fintype.card (D : Set V) = D.card := Fintype.card_coe D
    simpa only [hcard] using
      triangleInverse_abs_le (G.induce (D : Set V)) d M hd hM hcount x hx e

#print axioms arcs_neighbors_self_eq_trianglePairs
#print axioms incidence_inverse_of_diagonal_walks
#print axioms fourWalkSupply_of_arcs_pos
#print axioms incidenceBasis_of_arcs_pos

end PartitionedTriangleAbsorption.BlowupB.F0Direct.WalkConsequences
