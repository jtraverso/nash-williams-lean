/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.UniversalRefiner.Global
public import PartitionedTriangleAbsorption.AntiEdgeFamily

/-!
# Physical realisation of atoms

Given middle vertices `f r` for the requests `r ∈ s` (two-edge paths `(rt r).1 – f r – (rt r).2`
in the host graph, pairwise edge-disjoint and avoiding the reserve `X`), every atom becomes a
physical edge set (`phys`): a request becomes its path, a reserve edge stays itself.

On the domain `dom s X` of atoms, physical edge sets are pairwise disjoint, the vertex-degree
parities of a physical edge set are the atom boundary `rbOf rt`, and incidences add up.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.UniversalRefiner

open Finset AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- The physical edge set of an atom. -/
def phys (rt : Req V → V × V) (f : Req V → V) : Atom V → Finset (Sym2 V)
  | Sum.inl r => pathEdges (rt r).1 (rt r).2 (f r)
  | Sum.inr e => {e}

/-- The physical edge set of a finite set of atoms. -/
def physU (rt : Req V → V × V) (f : Req V → V) (A : Finset (Atom V)) : Finset (Sym2 V) :=
  A.biUnion (phys rt f)

/-- The atoms that are realised: the requests in `s` and the reserve edges. -/
def dom (s : Finset (Req V)) (X : Finset (Sym2 V)) : Finset (Atom V) :=
  s.image Sum.inl ∪ X.image Sum.inr

theorem card_phys_le (rt : Req V → V × V) (f : Req V → V) (a : Atom V) :
    (phys rt f a).card ≤ 2 := by
  rcases a with r | e
  · exact card_le_two
  · simp [phys]

theorem incidentLoad_singleton (e : Sym2 V) (w : V) :
    incidentLoad {e} w = if w ∈ e then 1 else 0 := by
  unfold incidentLoad
  rw [filter_singleton]
  split_ifs <;> simp

theorem incidentLoad_pathEdges {u v m w : V} (huv : u ≠ v) (hum : u ≠ m) (hvm : v ≠ m) :
    incidentLoad (pathEdges u v m) w =
      (if w = u then 1 else 0) + (if w = v then 1 else 0) + 2 * (if w = m then 1 else 0) := by
  have hne : s(u, m) ≠ s(v, m) := by
    intro h
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact huv h1
    · exact hum h1
  unfold incidentLoad pathEdges
  rw [filter_insert, filter_singleton]
  by_cases hwu : w = u
  · subst hwu
    have : w ≠ v := huv
    have : w ≠ m := hum
    simp [Sym2.mem_iff, *]
  · by_cases hwv : w = v
    · subst hwv
      simp [Sym2.mem_iff, hwu, hvm]
    · by_cases hwm : w = m
      · subst hwm
        simp [Sym2.mem_iff, hne, Ne.symm hum, Ne.symm hvm]
      · simp [Sym2.mem_iff, hwu, hwv, hwm]

section Realisation

variable {rt : Req V → V × V} {f : Req V → V} {s : Finset (Req V)} {X : Finset (Sym2 V)}
  {G : SimpleGraph V}

/-- The hypotheses on a realisation of the requests `s`. -/
structure Realises (G : SimpleGraph V) (X : Finset (Sym2 V)) (s : Finset (Req V))
    (rt : Req V → V × V) (f : Req V → V) : Prop where
  roots_ne : ∀ r ∈ s, (rt r).1 ≠ (rt r).2
  adj_left : ∀ r ∈ s, G.Adj (rt r).1 (f r)
  adj_right : ∀ r ∈ s, G.Adj (f r) (rt r).2
  avoid_left : ∀ r ∈ s, s((rt r).1, f r) ∉ X
  avoid_right : ∀ r ∈ s, s((rt r).2, f r) ∉ X
  disj : (s : Set (Req V)).PairwiseDisjoint fun r => pathEdges (rt r).1 (rt r).2 (f r)
  reserve : ∀ e ∈ X, e ∈ G.edgeSet

variable (hR : Realises G X s rt f)
include hR

theorem Realises.phys_subset {a : Atom V} (ha : a ∈ dom s X) :
    ∀ e ∈ phys rt f a, e ∈ G.edgeSet := by
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    intro e he
    simp only [phys, pathEdges, mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact (SimpleGraph.mem_edgeSet G).mpr (hR.adj_left r hr)
    · exact (SimpleGraph.mem_edgeSet G).mpr (hR.adj_right r hr).symm
  · obtain ⟨e, he, rfl⟩ := mem_image.mp ha
    intro e' he'
    simp only [phys, mem_singleton] at he'
    rw [he']
    exact hR.reserve e he

theorem Realises.phys_disjoint_X {r : Req V} (hr : r ∈ s) :
    Disjoint (phys rt f (Sum.inl r)) X := by
  rw [disjoint_left]
  intro e he heX
  simp only [phys, pathEdges, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact hR.avoid_left r hr heX
  · exact hR.avoid_right r hr heX

theorem Realises.pairwiseDisjoint :
    ((dom s X : Finset (Atom V)) : Set (Atom V)).PairwiseDisjoint (phys rt f) := by
  intro a ha b hb hab
  rcases mem_union.mp (mem_coe.mp ha) with ha | ha <;>
    rcases mem_union.mp (mem_coe.mp hb) with hb | hb
  · obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    obtain ⟨r', hr', rfl⟩ := mem_image.mp hb
    exact hR.disj hr hr' (fun h => hab (by rw [h]))
  · obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    obtain ⟨e, he, rfl⟩ := mem_image.mp hb
    exact disjoint_of_subset_right (by simpa [phys] using he) (hR.phys_disjoint_X hr)
  · obtain ⟨e, he, rfl⟩ := mem_image.mp ha
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hb
    exact (disjoint_of_subset_right (by simpa [phys] using he) (hR.phys_disjoint_X hr)).symm
  · obtain ⟨e, he, rfl⟩ := mem_image.mp ha
    obtain ⟨e', he', rfl⟩ := mem_image.mp hb
    have : e ≠ e' := fun h => hab (by rw [h])
    change Disjoint {e} {e'}
    simpa using this

theorem Realises.parity {a : Atom V} (ha : a ∈ dom s X) (w : V) :
    (incidentLoad (phys rt f a) w : ZMod 2) = rbOf rt a w := by
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨r, hr, rfl⟩ := mem_image.mp ha
    have h1 := hR.adj_left r hr
    have h2 := hR.adj_right r hr
    simp only [phys, rbOf, Pi.add_apply, ind]
    rw [incidentLoad_pathEdges (hR.roots_ne r hr) h1.ne h2.ne.symm]
    push_cast
    have : (2 : ZMod 2) = 0 := by decide
    rw [this, zero_mul, add_zero]
  · obtain ⟨e, he, rfl⟩ := mem_image.mp ha
    simp only [phys, rbOf, symInd]
    rw [incidentLoad_singleton]
    split_ifs <;> simp

theorem Realises.incidentLoad_physU {A : Finset (Atom V)} (hA : A ⊆ dom s X) (w : V) :
    incidentLoad (physU rt f A) w = ∑ a ∈ A, incidentLoad (phys rt f a) w :=
  ModThreeLayer.incidentLoad_biUnion_eq _ _ (hR.pairwiseDisjoint.subset (by exact_mod_cast hA)) w

theorem Realises.even_physU {A : Finset (Atom V)} (hA : A ⊆ dom s X)
    (h0 : ∑ a ∈ A, rbOf rt a = 0) (w : V) : Even (incidentLoad (physU rt f A) w) := by
  rw [← ZMod.natCast_eq_zero_iff_even, hR.incidentLoad_physU hA, Nat.cast_sum]
  rw [sum_congr rfl fun a ha => hR.parity (hA ha) w]
  have := congrFun h0 w
  simpa [Finset.sum_apply] using this

theorem Realises.disjoint_physU {A A' : Finset (Atom V)} (hA : A ⊆ dom s X)
    (hA' : A' ⊆ dom s X) (hd : Disjoint A A') : Disjoint (physU rt f A) (physU rt f A') := by
  unfold physU
  rw [disjoint_biUnion_left]
  intro a ha
  rw [disjoint_biUnion_right]
  intro b hb
  exact hR.pairwiseDisjoint (hA ha) (hA' hb) (fun h => disjoint_left.mp hd ha (h ▸ hb))

theorem Realises.card_physU {A : Finset (Req V)} (hA : A ⊆ s) :
    (physU rt f (A.image Sum.inl)).card = 2 * A.card := by
  unfold physU
  rw [image_biUnion]
  exact familyEdges_card A (fun r => (rt r).1) (fun r => (rt r).2) f
    (fun r hr => hR.roots_ne r (hA hr)) (hR.disj.subset (by exact_mod_cast hA))

omit hR in
theorem physU_subset_family {A : Finset (Req V)} (hA : A ⊆ s) :
    physU rt f (A.image Sum.inl) ⊆ familyEdges s (fun r => (rt r).1) (fun r => (rt r).2) f := by
  unfold physU familyEdges
  rw [image_biUnion]
  exact biUnion_subset_biUnion_of_subset_left _ hA

end Realisation

/-- Reserve parities: an even-degree edge set has zero total boundary. -/
theorem sum_symInd_eq_zero {L : Finset (Sym2 V)} (hL : ∀ v, Even (incidentLoad L v)) :
    ∑ π ∈ L, symInd π = 0 := by
  funext w
  have h := (ZMod.natCast_eq_zero_iff_even).mpr (hL w)
  unfold incidentLoad at h
  rw [card_filter] at h
  push_cast at h
  simpa [Finset.sum_apply, symInd] using h

end PartitionedTriangleAbsorption.UniversalRefiner
