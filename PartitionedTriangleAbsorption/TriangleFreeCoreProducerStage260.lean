/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TriangleFreeCoreStage260
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-! Construct the balanced link and its small exceptional set, rather than
assuming a connected transport core. Connectivity remains a later obligation. -/

@[expose] public section

namespace PartitionedTriangleAbsorption.TriangleFreeCoreStage260

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The dense triangle-free common link has size between n-2q and 2q.
Its vertices have ambient degree at most 3q and miss at most 4q-n vertices
in the complement. This is the geometric source of the exceptional-set bound. -/
theorem triangle_free_link_geometry (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (hdense : 3 * q < Fintype.card V) (u v : V)
    (htri : ∀ x ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ y ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      ∀ z ∈ univ.filter (fun x => G.Adj u x ∧ G.Adj v x),
      G.Adj x y → G.Adj x z → ¬ G.Adj y z) :
    let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
    (Fintype.card V : ℝ) - 2 * q ≤ S.card ∧ (S.card : ℝ) ≤ 2 * q ∧
      ∀ s ∈ S, (G.degree s : ℝ) ≤ 3 * q ∧
        ((univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x)).card : ℝ) ≤
          4 * q - Fintype.card V := by
  dsimp (config := { failIfUnchanged := false }) only
  let S := univ.filter (fun x => G.Adj u x ∧ G.Adj v x)
  have hlo : (Fintype.card V : ℝ) - 2 * q ≤ S.card :=
    common_link_size_lower G q hdeg u v
  have hS : q < (S.card : ℝ) := by linarith
  obtain ⟨hup, hd⟩ := triangle_free_size_and_degree G q hq hdeg S hS htri
  refine ⟨hlo, hup, ?_⟩
  intro s hs
  constructor
  · linarith [hd s hs]
  · linarith [triangle_free_cross_missing G q hdeg S hS htri hs]

/-- Double-count missing physical adjacencies. B is selected explicitly by
the threshold t in the complement of S; no size hypothesis on B is assumed. -/
theorem exceptional_set_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (t d : ℝ)
    (hmiss : ∀ s ∈ S,
      ((univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x)).card : ℝ) ≤ d) :
    let B := univ.filter (fun x => x ∉ S ∧
      t < ((S.filter (fun s => ¬ G.Adj x s)).card : ℝ))
    (B.card : ℝ) * t ≤ S.card * d := by
  classical
  dsimp (config := { failIfUnchanged := false }) only
  let B := univ.filter (fun x => x ∉ S ∧
    t < ((S.filter (fun s => ¬ G.Adj x s)).card : ℝ))
  have hcount := card_nsmul_le_card_nsmul
    (r := fun x s : V => ¬ G.Adj x s) (s := B) (t := S)
    (m := t) (n := d) (fun x hx => le_of_lt (mem_filter.mp hx).2.2)
    (fun s hs => show ((B.filter (fun x => ¬ G.Adj x s)).card : ℝ) ≤ d from by
      have hsub : B.filter (fun x => ¬ G.Adj x s) ⊆
          univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x) := by
        intro x hx
        obtain ⟨hxB, hxs⟩ := mem_filter.mp hx
        exact mem_filter.mpr ⟨mem_univ x, (mem_filter.mp hxB).2.1,
          fun h => hxs h.symm⟩
      have hc : ((B.filter (fun x => ¬ G.Adj x s)).card : ℝ) ≤
          (univ.filter (fun x => x ∉ S ∧ ¬ G.Adj s x)).card := by
        exact_mod_cast card_le_card hsub
      exact hc.trans (hmiss s hs))
  simpa only [nsmul_eq_mul] using hcount

omit [DecidableEq V] in
/-- Two disjoint triangle-free sets with controlled complements force many
low-degree vertices in the actual graph. This is the degree-population half
of the non-extremality contradiction, not a replacement definition of it. -/
theorem triangle_free_pair_low_degree_count (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S J : Finset V) (hdis : Disjoint S J)
    (hS : q < (S.card : ℝ)) (hJ : q < (J.card : ℝ))
    (htriS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (htriJ : ∀ x ∈ J, ∀ y ∈ J, ∀ z ∈ J,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (D : ℝ) (hDS : (Fintype.card V : ℝ) - S.card + q ≤ D)
    (hDJ : (Fintype.card V : ℝ) - J.card + q ≤ D) :
    S.card + J.card ≤ (univ.filter (fun v => (G.degree v : ℝ) ≤ D)).card := by
  classical
  obtain ⟨_, hdS⟩ := triangle_free_size_and_degree G q hq hdeg S hS htriS
  obtain ⟨_, hdJ⟩ := triangle_free_size_and_degree G q hq hdeg J hJ htriJ
  have hsub : S ∪ J ⊆ univ.filter (fun v => (G.degree v : ℝ) ≤ D) := by
    intro v hv
    refine mem_filter.mpr ⟨mem_univ v, ?_⟩
    rcases mem_union.mp hv with hv | hv
    · exact (hdS v hv).trans hDS
    · exact (hdJ v hv).trans hDJ
  simpa only [card_union_of_disjoint hdis] using card_le_card hsub

omit [DecidableEq V] in
/-- A triangle is forced in the surviving complementary set if the two
triangle-free pieces would account for too many low-degree vertices. -/
theorem triangle_in_survivor_of_low_degree_obstruction
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (q : ℝ) (hq : 0 ≤ q)
    (hdeg : ∀ v, (Fintype.card V : ℝ) ≤ G.degree v + q)
    (S J : Finset V) (hdis : Disjoint S J)
    (hS : q < (S.card : ℝ)) (hJ : q < (J.card : ℝ))
    (htriS : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z)
    (D : ℝ) (hDS : (Fintype.card V : ℝ) - S.card + q ≤ D)
    (hDJ : (Fintype.card V : ℝ) - J.card + q ≤ D)
    (hcount : (univ.filter (fun v => (G.degree v : ℝ) ≤ D)).card <
      S.card + J.card) :
    ∃ x ∈ J, ∃ y ∈ J, ∃ z ∈ J, G.Adj x y ∧ G.Adj x z ∧ G.Adj y z := by
  classical
  by_contra hno
  have htriJ : ∀ x ∈ J, ∀ y ∈ J, ∀ z ∈ J,
      G.Adj x y → G.Adj x z → ¬ G.Adj y z := by
    intro x hx y hy z hz hxy hxz hyz
    exact hno ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩
  have := triangle_free_pair_low_degree_count G q hq hdeg S J hdis hS hJ
    htriS htriJ D hDS hDJ
  omega

end PartitionedTriangleAbsorption.TriangleFreeCoreStage260
