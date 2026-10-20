/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-! Degree and cut geometry of a triangle-free common link.
These lemmas construct numerical bounds from physical adjacency; they do not
assume transport connectivity or a triangle decomposition. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.TriangleFreeCoreStage260

open Finset

variable {V : Type*} [Fintype V]

/-- Restricting a neighborhood loses at most the vertices outside S.
The real deficit q includes the vertex itself among the non-neighbors. -/
theorem restricted_degree_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S : Finset V) (v : V) :
    (S.card : ℝ) ≤ (S.filter (G.Adj v)).card + q := by
  classical
  have hc := card_union_add_card_inter S (G.neighborFinset v)
  have hu := card_le_univ (s := S ∪ G.neighborFinset v)
  have heq : S ∩ G.neighborFinset v = S.filter (G.Adj v) := by
    ext x
    simp
  rw [heq] at hc
  have hc' : ((S ∪ G.neighborFinset v).card : ℝ) +
      (S.filter (G.Adj v)).card = S.card + G.degree v := by
    exact_mod_cast hc
  have hu' : ((S ∪ G.neighborFinset v).card : ℝ) ≤ Fintype.card V := by
    exact_mod_cast hu
  linarith [hdeg v]

/-- In a triangle-free set larger than q, each internal neighborhood has at
most q vertices. A neighbor exists by the lower bound and supplies a disjoint
neighborhood against which to count. -/
theorem triangle_free_internal_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S : Finset V) (hS : q < (S.card : ℝ))
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    {u : V} (hu : u ∈ S) : (S.filter (G.Adj u)).card ≤ q := by
  classical
  have hlo := restricted_degree_lower G q hdeg S u
  have hp : 0 < (S.filter (G.Adj u)).card := by
    have : (0 : ℝ) < (S.filter (G.Adj u)).card := by linarith
    exact_mod_cast this
  obtain ⟨v, hv⟩ := card_pos.mp hp
  obtain ⟨hvS, huv⟩ := mem_filter.mp hv
  have hd : Disjoint (S.filter (G.Adj u)) (S.filter (G.Adj v)) := by
    rw [disjoint_left]
    intro w huw hvw
    exact htri u hu v hvS w (mem_filter.mp huw).1 huv
      (mem_filter.mp huw).2 (mem_filter.mp hvw).2
  have hc := card_le_card (show
      S.filter (G.Adj u) ∪ S.filter (G.Adj v) ⊆ S from by
    intro w hw
    rcases mem_union.mp hw with hw | hw
    · exact (mem_filter.mp hw).1
    · exact (mem_filter.mp hw).1)
  rw [card_union_of_disjoint hd] at hc
  have hc' : ((S.filter (G.Adj u)).card : ℝ) +
      (S.filter (G.Adj v)).card ≤ S.card := by exact_mod_cast hc
  linarith [restricted_degree_lower G q hdeg S v]

/-- Triangle-freeness bounds both the set size and all ambient degrees on it. -/
theorem triangle_free_size_and_degree (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S : Finset V) (hS : q < (S.card : ℝ))
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z) :
    (S.card : ℝ) ≤ 2 * q ∧
      ∀ u ∈ S, (G.degree u : ℝ) ≤ Fintype.card V - S.card + q := by
  classical
  have hp : 0 < S.card := by
    have : (0 : ℝ) < S.card := by linarith
    exact_mod_cast this
  obtain ⟨u, hu⟩ := card_pos.mp hp
  constructor
  · linarith [restricted_degree_lower G q hdeg S u,
      triangle_free_internal_upper G q hdeg S hS htri hu]
  · intro v hv
    have hc := card_union_add_card_inter S (G.neighborFinset v)
    have hu' := card_le_univ (s := S ∪ G.neighborFinset v)
    have heq : S ∩ G.neighborFinset v = S.filter (G.Adj v) := by
      ext x
      simp
    rw [heq] at hc
    have hc' : ((S ∪ G.neighborFinset v).card : ℝ) +
        (S.filter (G.Adj v)).card = S.card + G.degree v := by
      exact_mod_cast hc
    have hu'' : ((S ∪ G.neighborFinset v).card : ℝ) ≤ Fintype.card V := by
      exact_mod_cast hu'
    linarith [triangle_free_internal_upper G q hdeg S hS htri hv]

/-- A common neighborhood has at least n - 2q vertices, including when
the roots are not adjacent. -/
theorem common_link_size_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (u v : V) :
    (Fintype.card V : ℝ) - 2 * q ≤
      (univ.filter (fun x => G.Adj u x ∧ G.Adj v x)).card := by
  classical
  have hc := card_union_add_card_inter (G.neighborFinset u) (G.neighborFinset v)
  have hu := card_le_univ (s := G.neighborFinset u ∪ G.neighborFinset v)
  have heq : G.neighborFinset u ∩ G.neighborFinset v =
      univ.filter (fun x => G.Adj u x ∧ G.Adj v x) := by
    ext x
    simp
  rw [heq] at hc
  have hc' : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) +
      (univ.filter (fun x => G.Adj u x ∧ G.Adj v x)).card =
        G.degree u + G.degree v := by exact_mod_cast hc
  have hu' : ((G.neighborFinset u ∪ G.neighborFinset v).card : ℝ) ≤
      Fintype.card V := by exact_mod_cast hu
  linarith [hdeg u, hdeg v]

/-- If S is triangle-free and larger than q, each vertex in S misses at
most 2q-|S| vertices in its complement. -/
theorem triangle_free_cross_missing [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S : Finset V) (hS : q < (S.card : ℝ))
    (htri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    {u : V} (hu : u ∈ S) :
    ((univ.filter (fun x => x ∉ S ∧ ¬ G.Adj u x)).card : ℝ) ≤
      2 * q - S.card := by
  classical
  have hfilter : (univ.filter (fun x => ¬ G.Adj u x)).filter (fun x => x ∈ S) =
      S.filter (fun x => ¬ G.Adj u x) := by
    ext x
    simp [and_comm]
  have hpartition :
      (univ.filter (fun x => ¬ G.Adj u x)).card =
      (S.filter (fun x => ¬ G.Adj u x)).card +
      (univ.filter (fun x => x ∉ S ∧ ¬ G.Adj u x)).card := by
    have := card_filter_add_card_filter_not
      (s := univ.filter (fun x => ¬ G.Adj u x)) (p := fun x => x ∈ S)
    rw [hfilter] at this
    simpa [filter_filter, and_left_comm, and_comm, and_assoc] using this.symm
  have hwhole := card_filter_add_card_filter_not (s := (univ : Finset V))
    (p := G.Adj u)
  have hinside := card_filter_add_card_filter_not (s := S) (p := G.Adj u)
  have heq : univ.filter (G.Adj u) = G.neighborFinset u := by ext x; simp
  rw [heq] at hwhole
  have hp' : ((univ.filter (fun x => ¬ G.Adj u x)).card : ℝ) =
      (S.filter (fun x => ¬ G.Adj u x)).card +
      (univ.filter (fun x => x ∉ S ∧ ¬ G.Adj u x)).card := by
    exact_mod_cast hpartition
  have hw' : (G.degree u : ℝ) +
      (univ.filter (fun x => ¬ G.Adj u x)).card = Fintype.card V := by
    exact_mod_cast hwhole
  have hi' : ((S.filter (G.Adj u)).card : ℝ) +
      (S.filter (fun x => ¬ G.Adj u x)).card = S.card := by
    exact_mod_cast hinside
  linarith [hdeg u, triangle_free_internal_upper G q hdeg S hS htri hu]

end PartitionedTriangleAbsorption.TriangleFreeCoreStage260
