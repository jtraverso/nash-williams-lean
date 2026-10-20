/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic
public import PartitionedTriangleAbsorption.ReturnedBridge

/-! # Physical matching with prescribed neighbour-class inventories

The integer transport step alone does not provide graph edges. This module
constructs matchings in actual dense bipartite blocks. The quantitative
margin is explicit; the simultaneous packing of several stars is separate.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalStarMatching

open Finset

/-- Hall's condition follows from a bound on missing neighbours on both sides. -/
theorem dense_hall {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]
    (R : A → B → Prop) [DecidableRel R] (r : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hsize : 2 * r ≤ Fintype.card B)
    (hleft : ∀ a, (univ.filter fun b => ¬ R a b).card ≤ r)
    (hright : ∀ b, (univ.filter fun a => ¬ R a b).card ≤ r)
    (s : Finset A) :
    s.card ≤ (s.biUnion fun a => univ.filter (R a)).card := by
  classical
  by_cases hs : s = ∅
  · simp [hs]
  obtain ⟨a, ha⟩ := nonempty_iff_ne_empty.mpr hs
  by_cases hsmall : s.card ≤ Fintype.card B - r
  · have hc := card_filter_add_card_filter_not (s := (univ : Finset B)) (R a)
    have hm := hleft a
    have hsub : univ.filter (R a) ⊆ s.biUnion (fun a => univ.filter (R a)) :=
      subset_biUnion_of_mem (fun a => univ.filter (R a)) ha
    have hb := card_le_card hsub
    simp only [card_univ] at hc
    omega
  · have he : s.biUnion (fun a => univ.filter (R a)) = univ := by
      apply eq_univ_of_forall
      intro b
      by_contra hb
      have hsub : s ⊆ univ.filter (fun a => ¬ R a b) := by
        intro a ha
        apply mem_filter.mpr
        refine ⟨mem_univ _, ?_⟩
        intro hab
        exact hb (mem_biUnion.mpr ⟨a, ha, mem_filter.mpr ⟨mem_univ _, hab⟩⟩)
      have hc := card_le_card hsub
      have hm := hright b
      omega
    rw [he, card_univ, ← hcard]
    exact card_le_univ s

/-- A perfect matching using only pairs in the supplied physical relation. -/
theorem exists_dense_matching {A B : Type*} [Fintype A] [Fintype B]
    (R : A → B → Prop) [DecidableRel R] (r : ℕ)
    (hcard : Fintype.card A = Fintype.card B)
    (hsize : 2 * r ≤ Fintype.card B)
    (hleft : ∀ a, (univ.filter fun b => ¬ R a b).card ≤ r)
    (hright : ∀ b, (univ.filter fun a => ¬ R a b).card ≤ r) :
    ∃ f : A → B, Function.Bijective f ∧ ∀ a, R a (f a) := by
  classical
  obtain ⟨f, hf, hR⟩ := (all_card_le_biUnion_card_iff_existsInjective'
    (fun a => univ.filter (R a))).mp (dense_hall R r hcard hsize hleft hright)
  refine ⟨f, ?_, fun a => (mem_filter.mp (hR a)).2⟩
  exact (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem subtype_filter_card (Y : Finset V) (P : V → Prop) [DecidablePred P] :
    ((univ : Finset Y).filter fun (y : Y) => P y.val).card = (Y.filter P).card := by
  classical
  apply card_bij (s := (univ : Finset Y).filter fun (y : Y) => P y.val)
    (t := Y.filter P) (fun (y : Y) _ => y.val)
  · intro y hy
    exact mem_filter.mpr ⟨y.property, (mem_filter.mp hy).2⟩
  · intro a _ b _ hab
    exact Subtype.ext hab
  · intro y hy
    refine ⟨⟨y, (mem_filter.mp hy).1⟩, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hy).2⟩

omit [DecidableEq V] in
/-- The matching is a bijection between actual vertex sets, and every chosen
pair is an edge of the graph. -/
theorem exists_matching_between_sets (G : SimpleGraph V) [DecidableRel G.Adj]
    (X Y : Finset V) (r : ℕ) (hcard : X.card = Y.card) (hsize : 2 * r ≤ Y.card)
    (hleft : ∀ x ∈ X, (Y.filter fun y => ¬ G.Adj x y).card ≤ r)
    (hright : ∀ y ∈ Y, (X.filter fun x => ¬ G.Adj x y).card ≤ r) :
    ∃ f : X ≃ Y, ∀ x : X, G.Adj x (f x) := by
  classical
  obtain ⟨f, hf, hG⟩ := exists_dense_matching
    (fun (x : X) (y : Y) => G.Adj x y) r
    (by simpa only [Fintype.card_coe] using hcard)
    (by simpa only [Fintype.card_coe] using hsize)
    (fun x => by
      rw [subtype_filter_card Y (fun y => ¬ G.Adj (x : V) y)]
      exact hleft x x.property)
    (fun y => by
      rw [subtype_filter_card X (fun x => ¬ G.Adj x (y : V))]
      exact hright y y.property)
  exact ⟨Equiv.ofBijective f hf, hG⟩

theorem triangle_left_membership (z : V) (X Y : Finset V) (f : X ≃ Y)
    (hz : z ∉ X) (hXY : Disjoint X Y) (a : X) (w : V) (hw : w ∈ X) :
    w ∈ ({z, (a : V), (f a : V)} : Finset V) ↔ w = a := by
  have hwz : w ≠ z := fun h => hz (h ▸ hw)
  have hwf : w ≠ (f a : V) := fun h =>
    disjoint_left.mp hXY hw (h.symm ▸ (f a).property)
  simp [hwz, hwf]

theorem triangle_right_membership (z : V) (X Y : Finset V) (f : X ≃ Y)
    (hz : z ∉ Y) (hXY : Disjoint X Y) (a : X) (w : V) (hw : w ∈ Y) :
    w ∈ ({z, (a : V), (f a : V)} : Finset V) ↔ w = (f a : V) := by
  have hwz : w ≠ z := fun h => hz (h ▸ hw)
  have hwa : w ≠ (a : V) := fun h =>
    disjoint_left.mp hXY a.property (h ▸ hw)
  simp [hwz, hwa]

/-- Distinct matching pairs give edge-disjoint triangles through the root. -/
theorem star_triangles_disjoint (z : V) (X Y : Finset V) (f : X ≃ Y)
    (hzX : z ∉ X) (hzY : z ∉ Y) (hXY : Disjoint X Y) :
    (Set.univ : Set X).PairwiseDisjoint
      (fun a => triEdges {z, (a : V), (f a : V)}) := by
  classical
  intro a _ b _ hab
  have hza : z ≠ (a : V) := fun h => hzX (h.symm ▸ a.property)
  have hzb : z ≠ (b : V) := fun h => hzX (h.symm ▸ b.property)
  have hzf : z ≠ (f a : V) := fun h => hzY (h.symm ▸ (f a).property)
  have hzg : z ≠ (f b : V) := fun h => hzY (h.symm ▸ (f b).property)
  have haa : (a : V) ≠ (b : V) := fun h => hab (Subtype.ext h)
  have hff : (f a : V) ≠ (f b : V) := fun h => hab (f.injective (Subtype.ext h))
  have hcross (x : X) (y : Y) : (x : V) ≠ (y : V) := fun h =>
    disjoint_left.mp hXY x.property (h.symm ▸ y.property)
  change Disjoint (triEdges {z, (a : V), (f a : V)})
    (triEdges {z, (b : V), (f b : V)})
  rw [triEdges_three hza hzf (hcross a (f a)),
    triEdges_three hzb hzg (hcross b (f b)), disjoint_left]
  intro e he he'
  simp only [mem_insert, mem_singleton] at he he'
  rcases he with rfl | rfl | rfl <;>
    simp [haa, hff, hza.symm, hzb, hzg,
      (hcross b (f a)).symm, hcross a (f b)] at he'

/-- A physical triangle packing for one prescribed bipartite block of a star.
The number of triangles is the common block cardinality. -/
theorem exists_dense_star_block [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V) (X Y : Finset V) (r : ℕ)
    (hXY : Disjoint X Y) (hX : X ⊆ G.neighborFinset z) (hY : Y ⊆ G.neighborFinset z)
    (hcard : X.card = Y.card) (hsize : 2 * r ≤ Y.card)
    (hleft : ∀ x ∈ X, (Y.filter fun y => ¬ G.Adj x y).card ≤ r)
    (hright : ∀ y ∈ Y, (X.filter fun x => ¬ G.Adj x y).card ≤ r) :
    ∃ (f : X ≃ Y) (D : Finset (Finset V)),
      D = univ.image (fun a : X => {z, (a : V), (f a : V)}) ∧
      (∀ T ∈ D, G.IsNClique 3 T) ∧
      (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
      D.card = X.card ∧
      ∀ w ∈ X ∪ Y, ∃! T, T ∈ D ∧ z ∈ T ∧ w ∈ T := by
  classical
  obtain ⟨f, hf⟩ := exists_matching_between_sets G X Y r hcard hsize hleft hright
  have hzN : z ∉ G.neighborFinset z := by simp
  have hzX : z ∉ X := fun h => hzN (hX h)
  have hzY : z ∉ Y := fun h => hzN (hY h)
  let tri (a : X) : Finset V := {z, (a : V), (f a : V)}
  let D := univ.image tri
  have hinj : Function.Injective tri := by
    intro a b he
    have ha : (a : V) ∈ tri b := he ▸ (by simp [tri])
    exact Subtype.ext ((triangle_left_membership z X Y f hzX hXY b a a.property).mp ha)
  have hdis := star_triangles_disjoint z X Y f hzX hzY hXY
  refine ⟨f, D, rfl, ?_, ?_, ?_, ?_⟩
  · intro T hT
    obtain ⟨a, _, rfl⟩ := mem_image.mp hT
    apply G.is3Clique_triple_iff.mpr
    exact ⟨(G.mem_neighborFinset z a).mp (hX a.property),
      (G.mem_neighborFinset z (f a)).mp (hY (f a).property), hf a⟩
  · intro T hT U hU hTU
    obtain ⟨a, _, rfl⟩ := mem_image.mp hT
    obtain ⟨b, _, rfl⟩ := mem_image.mp hU
    exact hdis (Set.mem_univ a) (Set.mem_univ b) (fun h => hTU (congrArg tri h))
  · rw [card_image_of_injective _ hinj]
    simp only [card_univ, Fintype.card_coe]
  · intro w hwN
    rcases mem_union.mp hwN with hwX | hwY
    · let a : X := ⟨w, hwX⟩
      refine ⟨tri a, ⟨mem_image.mpr ⟨a, mem_univ _, rfl⟩, by simp [tri], by simp [tri, a]⟩, ?_⟩
      intro T hT
      obtain ⟨b, _, rfl⟩ := mem_image.mp hT.1
      have he := (triangle_left_membership z X Y f hzX hXY b w hwX).mp hT.2.2
      have hba : b = a := Subtype.ext he.symm
      exact congrArg tri hba
    · let a : X := f.symm ⟨w, hwY⟩
      have ha : (f a : V) = w := by simp [a]
      refine ⟨tri a, ⟨mem_image.mpr ⟨a, mem_univ _, rfl⟩, by simp [tri], by simp [tri, ha]⟩, ?_⟩
      intro T hT
      obtain ⟨b, _, rfl⟩ := mem_image.mp hT.1
      have he := (triangle_right_membership z X Y f hzY hXY b w hwY).mp hT.2.2
      have hba : b = a := f.injective (Subtype.ext (he.symm.trans ha.symm))
      exact congrArg tri hba

/-- If the two blocks partition the root's entire neighbourhood, the constructed
packing covers every incident edge exactly once. -/
theorem exists_dense_star_packing [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : V) (X Y : Finset V) (r : ℕ)
    (hXY : Disjoint X Y) (hcover : X ∪ Y = G.neighborFinset z)
    (hcard : X.card = Y.card) (hsize : 2 * r ≤ Y.card)
    (hleft : ∀ x ∈ X, (Y.filter fun y => ¬ G.Adj x y).card ≤ r)
    (hright : ∀ y ∈ Y, (X.filter fun x => ¬ G.Adj x y).card ≤ r) :
    ∃ (f : X ≃ Y) (D : Finset (Finset V)),
      D = univ.image (fun a : X => {z, (a : V), (f a : V)}) ∧
      (∀ T ∈ D, G.IsNClique 3 T) ∧
      (D : Set (Finset V)).PairwiseDisjoint triEdges ∧
      D.card = X.card ∧
      ∀ w, G.Adj z w → ∃! T, T ∈ D ∧ z ∈ T ∧ w ∈ T := by
  obtain ⟨f, D, he, htri, hdis, hcount, hroot⟩ := exists_dense_star_block G z X Y r hXY
    (fun _ hx => hcover ▸ mem_union_left Y hx)
    (fun _ hy => hcover ▸ mem_union_right X hy) hcard hsize hleft hright
  refine ⟨f, D, he, htri, hdis, hcount, ?_⟩
  intro w hw
  exact hroot w (hcover.symm ▸ (G.mem_neighborFinset z w).mpr hw)

end PartitionedTriangleAbsorption.PhysicalStarMatching
