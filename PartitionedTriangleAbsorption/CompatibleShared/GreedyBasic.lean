/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SharedLibrarySelection

/-! # Shared-library greedy embedding: definitions and counting lemmas

A finite library `B j` (`j ∈ idx`) of edge sets on an abstract identity type `A`.
`libLoad v = ∑ j, deg_{B j}(v)` is the multiplicity load and `libSize = ∑ j, |B j|`.
The vertex support `vsupp E` of an edge set is exactly its set of incident vertices.
No finiteness of `A` is assumed: all supports are finite because the library is.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SharedGreedyPort

open Finset AntiEdgeSelection

variable {A V I : Type*} [DecidableEq A] [DecidableEq V]

/-- The edge union of the library. -/
def libU (idx : Finset I) (B : I → Finset (Sym2 A)) : Finset (Sym2 A) := idx.biUnion B

/-- The library multiplicity load `L(v) = ∑_j deg_{B_j}(v)`. -/
def libLoad (idx : Finset I) (B : I → Finset (Sym2 A)) (v : A) : ℕ :=
  ∑ j ∈ idx, incidentLoad (B j) v

/-- The total library size `S = ∑_j |B_j|`. -/
def libSize (idx : Finset I) (B : I → Finset (Sym2 A)) : ℕ := ∑ j ∈ idx, (B j).card

/-- The vertex support of an edge set: exactly its incident vertices. -/
def vsupp (E : Finset (Sym2 A)) : Finset A := E.biUnion Sym2.toFinset

/-- Two identities coappear if both are incident with one library piece. -/
def Coappear (idx : Finset I) (B : I → Finset (Sym2 A)) (u w : A) : Prop :=
  ∃ j ∈ idx, u ∈ vsupp (B j) ∧ w ∈ vsupp (B j)

/-- Library neighbours of `v`. -/
def nbrs (idx : Finset I) (B : I → Finset (Sym2 A)) (v : A) : Finset A :=
  (vsupp (libU idx B)).filter fun u => s(u, v) ∈ libU idx B

/-- Earlier library neighbours of `v` for the rank `rk`; roots count as earlier. -/
def earlier (idx : Finset I) (B : I → Finset (Sym2 A)) (R : Finset A) (rk : A → ℕ)
    (v : A) : Finset A :=
  (nbrs idx B v).filter fun u => u ∈ R ∨ rk u < rk v

/-- Library edges with both ends in `P`. -/
def placedE (idx : Finset I) (B : I → Finset (Sym2 A)) (P : Finset A) : Finset (Sym2 A) :=
  (libU idx B).filter fun e => e.toFinset ⊆ P

/-- The physical load of a partial placement: `load(y) = ∑_{v ∈ P, g v = y} L(v)`. -/
def placedLoad (idx : Finset I) (B : I → Finset (Sym2 A)) (P : Finset A) (g : A → V)
    (y : V) : ℕ :=
  ∑ v ∈ P.filter (fun v => g v = y), libLoad idx B v

omit [DecidableEq A] [DecidableEq V] in
theorem map_pair (f : A → V) (a b : A) : Sym2.map f s(a, b) = s(f a, f b) := rfl

omit [DecidableEq V] in
theorem mem_vsupp {E : Finset (Sym2 A)} {v : A} : v ∈ vsupp E ↔ ∃ e ∈ E, v ∈ e := by
  simp [vsupp, Sym2.mem_toFinset]

omit [DecidableEq V] in
theorem mem_libU {idx : Finset I} {B : I → Finset (Sym2 A)} {e : Sym2 A} :
    e ∈ libU idx B ↔ ∃ j ∈ idx, e ∈ B j := by
  simp [libU]

omit [DecidableEq V] in
theorem card_toFinset_le_two (e : Sym2 A) : e.toFinset.card ≤ 2 := by
  induction e using Sym2.ind with
  | _ a b => rw [Sym2.toFinset_mk_eq]; exact card_le_two

omit [DecidableEq V] in
theorem card_vsupp_le (E : Finset (Sym2 A)) : (vsupp E).card ≤ 2 * E.card := by
  refine card_biUnion_le.trans ?_
  calc ∑ e ∈ E, e.toFinset.card ≤ ∑ _e ∈ E, 2 := sum_le_sum fun e _ => card_toFinset_le_two e
    _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]

omit [DecidableEq V] in
theorem incidentLoad_mono {E E' : Finset (Sym2 A)} (h : E ⊆ E') (u : A) :
    incidentLoad E u ≤ incidentLoad E' u :=
  card_le_card (filter_subset_filter _ h)

omit [DecidableEq V] in
theorem incidentLoad_union_le (E E' : Finset (Sym2 A)) (u : A) :
    incidentLoad (E ∪ E') u ≤ incidentLoad E u + incidentLoad E' u := by
  unfold incidentLoad
  rw [filter_union]
  exact card_union_le _ _

omit [DecidableEq V] in
theorem incidentLoad_pos {E : Finset (Sym2 A)} {u : A} (h : u ∈ vsupp E) :
    0 < incidentLoad E u := by
  obtain ⟨e, he, hu⟩ := mem_vsupp.mp h
  exact card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hu⟩⟩

omit [DecidableEq V] in
/-- Handshake bound with an arbitrary vertex set. -/
theorem sum_incidentLoad_le (E : Finset (Sym2 A)) (P : Finset A) :
    ∑ u ∈ P, incidentLoad E u ≤ 2 * E.card := by
  have h : ∑ u ∈ P, incidentLoad E u = ∑ e ∈ E, (P.filter fun u => u ∈ e).card := by
    simp only [incidentLoad, card_filter]
    exact sum_comm
  rw [h]
  calc ∑ e ∈ E, (P.filter fun u => u ∈ e).card ≤ ∑ _e ∈ E, 2 := by
        refine sum_le_sum fun e _ => ?_
        refine (card_le_card ?_).trans (card_toFinset_le_two e)
        intro u hu
        exact Sym2.mem_toFinset.mpr (mem_filter.mp hu).2
    _ = 2 * E.card := by rw [sum_const, smul_eq_mul, mul_comm]

omit [DecidableEq V] in
theorem sum_libLoad_le (idx : Finset I) (B : I → Finset (Sym2 A)) (P : Finset A) :
    ∑ u ∈ P, libLoad idx B u ≤ 2 * libSize idx B := by
  unfold libLoad libSize
  rw [sum_comm, mul_sum]
  exact sum_le_sum fun j _ => sum_incidentLoad_le (B j) P

omit [DecidableEq V] in
theorem incidentLoad_libU_le (idx : Finset I) (B : I → Finset (Sym2 A)) (u : A) :
    incidentLoad (libU idx B) u ≤ libLoad idx B u := by
  unfold incidentLoad libU libLoad
  rw [filter_biUnion]
  exact card_biUnion_le

omit [DecidableEq V] in
/-- An identity shares a piece with at most `2 b L(v)` identities. -/
theorem card_coappear_le (idx : Finset I) (B : I → Finset (Sym2 A)) (b : ℕ)
    (hcard : ∀ j ∈ idx, (B j).card ≤ b) (P : Finset A) (v : A)
    [DecidablePred fun u => Coappear idx B u v] :
    (P.filter fun u => Coappear idx B u v).card ≤ 2 * b * libLoad idx B v := by
  classical
  let J := idx.filter fun j => v ∈ vsupp (B j)
  have hsub : (P.filter fun u => Coappear idx B u v) ⊆ J.biUnion fun j => vsupp (B j) := by
    intro u hu
    obtain ⟨j, hj, hu, hv⟩ := (mem_filter.mp hu).2
    exact mem_biUnion.mpr ⟨j, mem_filter.mpr ⟨hj, hv⟩, hu⟩
  have hJ : J.card ≤ libLoad idx B v := by
    rw [card_filter]
    refine sum_le_sum fun j _ => ?_
    split_ifs with h
    · exact incidentLoad_pos h
    · exact Nat.zero_le _
  calc (P.filter fun u => Coappear idx B u v).card
      ≤ ∑ j ∈ J, (vsupp (B j)).card := (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ _j ∈ J, 2 * b := sum_le_sum fun j hj =>
        (card_vsupp_le _).trans (by have := hcard j (mem_filter.mp hj).1; omega)
    _ = J.card * (2 * b) := by rw [sum_const, smul_eq_mul]
    _ ≤ libLoad idx B v * (2 * b) := Nat.mul_le_mul_right _ hJ
    _ = 2 * b * libLoad idx B v := Nat.mul_comm _ _

/-- The image of an edge set has incidences only through fibres. -/
theorem incidentLoad_image_le (g : A → V) (E : Finset (Sym2 A)) (P : Finset A)
    (hE : ∀ e ∈ E, ∀ x ∈ e, x ∈ P) (y : V) :
    incidentLoad (E.image (Sym2.map g)) y ≤
      ∑ u ∈ P.filter (fun u => g u = y), incidentLoad E u := by
  have hsub : (E.image (Sym2.map g)).filter (fun e => y ∈ e) ⊆
      ((P.filter fun u => g u = y).biUnion fun u => E.filter fun e => u ∈ e).image
        (Sym2.map g) := by
    intro e' he'
    obtain ⟨he', hy⟩ := mem_filter.mp he'
    obtain ⟨e, he, rfl⟩ := mem_image.mp he'
    obtain ⟨x, hx, rfl⟩ := Sym2.mem_map.mp hy
    exact mem_image.mpr ⟨e, mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨hE e he x hx, rfl⟩,
      mem_filter.mpr ⟨he, hx⟩⟩, rfl⟩
  exact (card_le_card hsub).trans (card_image_le.trans card_biUnion_le)

omit [DecidableEq A] [DecidableEq V] in
theorem map_congr_of_eqOn {f g : A → V} {e : Sym2 A} (h : ∀ x ∈ e, f x = g x) :
    Sym2.map f e = Sym2.map g e := by
  induction e using Sym2.ind with
  | _ a b =>
    simp only [map_pair]
    rw [h a (Sym2.mem_mk_left a b), h b (Sym2.mem_mk_right a b)]

variable [Fintype V]

/-- Total physical load is the total library load of the placed identities. -/
theorem sum_placedLoad (idx : Finset I) (B : I → Finset (Sym2 A)) (P : Finset A)
    (g : A → V) : ∑ y, placedLoad idx B P g y = ∑ v ∈ P, libLoad idx B v := by
  unfold placedLoad
  exact sum_fiberwise P g _

end PartitionedTriangleAbsorption.SharedGreedyPort
