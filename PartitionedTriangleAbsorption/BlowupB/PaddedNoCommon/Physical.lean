/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNoCommon.Paths

@[expose] public section

/-!
# Physicalization of a virtual refiner

A refiner run in the complete graph returns pieces made of reserve edges (in `X`) and virtual
edges (in `R`). Replacing every virtual edge `e ∈ R` by its physical path `physPath x y z e` and
keeping every reserve edge gives physical pieces (`physPiece`). If the paths are edge-disjoint and
avoid `X`, then:

* disjoint pieces stay disjoint, and the image of `R ∪ L` is `R' ∪ L` with `R' = physPiece R`;
  hence the refinement property transfers verbatim, for every `L ⊆ X` (`physPiece_refines`);
* degrees change by even amounts and the number of edges by multiples of three
  (`physPiece_even3`), so `Even3` pieces stay `Even3`;
* sizes grow at most by the factor `4`.
-/

namespace PaddedNoCommon

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Reserve edges are kept, virtual edges are replaced by their paths. -/
noncomputable def physMap (X : Finset (Sym2 V)) (x y z : Sym2 V → V) (e : Sym2 V) :
    Finset (Sym2 V) :=
  if e ∈ X then {e} else physPath x y z e

/-- The physical image of an edge set. -/
noncomputable def physPiece (X : Finset (Sym2 V)) (x y z : Sym2 V → V) (B : Finset (Sym2 V)) :
    Finset (Sym2 V) :=
  B.biUnion (physMap X x y z)

/-- The hypotheses on a path system for the virtual edges `R`. -/
structure PathSystem (G : SimpleGraph V) (X R : Finset (Sym2 V)) (x y z : Sym2 V → V) : Prop where
  disjRX : Disjoint R X
  loop : ∀ e ∈ R, ¬ e.IsDiag
  path : ∀ e ∈ R, IsPath4 G (endU e) (x e) (y e) (z e) (endV e)
  avoid : ∀ e ∈ R, Disjoint (physPath x y z e) X
  disj : ∀ e ∈ R, ∀ e' ∈ R, e ≠ e' → Disjoint (physPath x y z e) (physPath x y z e')

namespace PathSystem

variable {G : SimpleGraph V} {X R : Finset (Sym2 V)} {x y z : Sym2 V → V}

theorem physMap_of_R (h : PathSystem G X R x y z) {e : Sym2 V} (he : e ∈ R) :
    physMap X x y z e = physPath x y z e := by
  have : e ∉ X := fun hX => disjoint_left.mp h.disjRX he hX
  simp only [physMap, if_neg this]

theorem physMap_of_X {e : Sym2 V} (he : e ∈ X) : physMap X x y z e = {e} := by
  simp only [physMap, if_pos he]

theorem physMap_disjoint (h : PathSystem G X R x y z) {e e' : Sym2 V} (he : e ∈ X ∪ R)
    (he' : e' ∈ X ∪ R) (hne : e ≠ e') :
    Disjoint (physMap X x y z e) (physMap X x y z e') := by
  rcases mem_union.mp he with heX | heR <;> rcases mem_union.mp he' with he'X | he'R
  · rw [physMap_of_X heX, physMap_of_X he'X]
    exact disjoint_singleton.mpr hne
  · rw [physMap_of_X heX, h.physMap_of_R he'R]
    exact disjoint_singleton_left.mpr fun hm => disjoint_left.mp (h.avoid e' he'R) hm heX
  · rw [physMap_of_X he'X, h.physMap_of_R heR]
    exact disjoint_singleton_right.mpr fun hm => disjoint_left.mp (h.avoid e heR) hm he'X
  · rw [h.physMap_of_R heR, h.physMap_of_R he'R]
    exact h.disj e heR e' he'R hne

theorem physMap_subset [DecidableRel G.Adj] (h : PathSystem G X R x y z)
    (hXG : X ⊆ G.edgeFinset) {e : Sym2 V} (he : e ∈ X ∪ R) :
    physMap X x y z e ⊆ G.edgeFinset := by
  rcases mem_union.mp he with heX | heR
  · rw [physMap_of_X heX]; exact singleton_subset_iff.mpr (hXG heX)
  · rw [h.physMap_of_R heR]; exact pathEdges_subset (h.path e heR)

theorem physMap_card (h : PathSystem G X R x y z) {e : Sym2 V} (he : e ∈ X ∪ R) :
    (physMap X x y z e).card = if e ∈ X then 1 else 4 := by
  rcases mem_union.mp he with heX | heR
  · rw [physMap_of_X heX, card_singleton, if_pos heX]
  · have : e ∉ X := fun hX => disjoint_left.mp h.disjRX heR hX
    rw [h.physMap_of_R heR, if_neg this]
    exact pathEdges_card (ends_ne (h.loop e heR)) (h.path e heR)

theorem physMap_incidentLoad (h : PathSystem G X R x y z) {e : Sym2 V} (he : e ∈ X ∪ R)
    (w : V) :
    incidentLoad (physMap X x y z e) w = incidentLoad {e} w +
      2 * (if e ∉ X ∧ (w = x e ∨ w = y e ∨ w = z e) then 1 else 0) := by
  rcases mem_union.mp he with heX | heR
  · rw [physMap_of_X heX]
    simp [heX]
  · have hnX : e ∉ X := fun hX => disjoint_left.mp h.disjRX heR hX
    rw [h.physMap_of_R heR]
    unfold physPath
    rw [pathEdges_incidentLoad (ends_ne (h.loop e heR)) (h.path e heR), mk_ends]
    simp only [hnX, not_false_eq_true, true_and]

theorem physPiece_card (h : PathSystem G X R x y z) {B : Finset (Sym2 V)} (hB : B ⊆ X ∪ R) :
    (physPiece X x y z B).card = ∑ e ∈ B, if e ∈ X then 1 else 4 := by
  unfold physPiece
  rw [card_biUnion]
  · exact sum_congr rfl fun e he => h.physMap_card (hB he)
  · intro e he e' he' hne
    exact h.physMap_disjoint (hB he) (hB he') hne

theorem physPiece_incidentLoad (h : PathSystem G X R x y z) {B : Finset (Sym2 V)}
    (hB : B ⊆ X ∪ R) (w : V) :
    incidentLoad (physPiece X x y z B) w = incidentLoad B w +
      2 * ∑ e ∈ B, (if e ∉ X ∧ (w = x e ∨ w = y e ∨ w = z e) then 1 else 0) := by
  have h1 : incidentLoad (physPiece X x y z B) w =
      ∑ e ∈ B, incidentLoad (physMap X x y z e) w := by
    unfold physPiece incidentLoad
    rw [filter_biUnion, card_biUnion]
    intro e he e' he' hne
    exact disjoint_filter_filter (h.physMap_disjoint (hB he) (hB he') hne)
  rw [h1, sum_congr rfl fun e he => h.physMap_incidentLoad (hB he) w, sum_add_distrib,
    ← mul_sum]
  congr 1
  rw [incidentLoad_eq_sum]
  exact sum_congr rfl fun e _ => by rw [incidentLoad_eq_sum, sum_singleton]

theorem physPiece_even3 (h : PathSystem G X R x y z) {B : Finset (Sym2 V)} (hB : B ⊆ X ∪ R)
    (hB3 : OnePart.Even3 B) : OnePart.Even3 (physPiece X x y z B) := by
  obtain ⟨h3, hev⟩ := hB3
  refine ⟨?_, fun w => ?_⟩
  · rw [h.physPiece_card hB]
    have hmod : ∀ e ∈ B, (if e ∈ X then 1 else 4) = 1 + 3 * (if e ∈ X then 0 else 1) := by
      intro e _; split_ifs <;> rfl
    rw [sum_congr rfl hmod, sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, mul_one]
    exact dvd_add h3 (dvd_mul_right _ _)
  · rw [h.physPiece_incidentLoad hB w]
    exact (hev w).add (even_two_mul _)

theorem physPiece_card_le (h : PathSystem G X R x y z) {B : Finset (Sym2 V)}
    (hB : B ⊆ X ∪ R) : (physPiece X x y z B).card ≤ 4 * B.card := by
  rw [h.physPiece_card hB, card_eq_sum_ones, mul_sum]
  exact sum_le_sum fun e _ => by split_ifs <;> omega

theorem physPiece_subset_G [DecidableRel G.Adj] (h : PathSystem G X R x y z)
    (hXG : X ⊆ G.edgeFinset) {B : Finset (Sym2 V)} (hB : B ⊆ X ∪ R) :
    physPiece X x y z B ⊆ G.edgeFinset :=
  biUnion_subset.mpr fun e he => h.physMap_subset hXG (hB he)

theorem physPiece_of_subset_X {L : Finset (Sym2 V)} (hL : L ⊆ X) :
    physPiece X x y z L = L := by
  unfold physPiece
  rw [biUnion_congr rfl fun e he => physMap_of_X (hL he)]
  exact biUnion_singleton_eq_self

theorem physPiece_R (h : PathSystem G X R x y z) :
    physPiece X x y z R = R.biUnion (physPath x y z) :=
  biUnion_congr rfl fun _ he => h.physMap_of_R he

theorem physPiece_subset (h : PathSystem G X R x y z) {B : Finset (Sym2 V)}
    (hB : B ⊆ X ∪ R) : physPiece X x y z B ⊆ X ∪ R.biUnion (physPath x y z) := by
  intro f hf
  obtain ⟨e, he, hfe⟩ := mem_biUnion.mp hf
  rcases mem_union.mp (hB he) with heX | heR
  · rw [physMap_of_X heX] at hfe
    rw [mem_singleton.mp hfe]
    exact mem_union_left _ heX
  · rw [h.physMap_of_R heR] at hfe
    exact mem_union_right _ (mem_biUnion.mpr ⟨e, heR, hfe⟩)

theorem physPiece_disjoint (h : PathSystem G X R x y z) {B B' : Finset (Sym2 V)}
    (hB : B ⊆ X ∪ R) (hB' : B' ⊆ X ∪ R) (hd : Disjoint B B') :
    Disjoint (physPiece X x y z B) (physPiece X x y z B') := by
  unfold physPiece
  rw [disjoint_biUnion_left]
  intro e he
  rw [disjoint_biUnion_right]
  intro e' he'
  exact h.physMap_disjoint (hB he) (hB' he') (fun heq => disjoint_left.mp hd he (heq ▸ he'))

/-- **The refinement property transfers to the physical pieces.** -/
theorem physPiece_refines {I : Type*} [DecidableEq I] (h : PathSystem G X R x y z)
    (P : I → Finset (Sym2 V)) (s : Finset I) (hP : ∀ i ∈ s, P i ⊆ X ∪ R)
    (hdis : (s : Set I).PairwiseDisjoint P) (L : Finset (Sym2 V)) (hL : L ⊆ X)
    (hU : s.biUnion P = R ∪ L) :
    (s : Set I).PairwiseDisjoint (fun i => physPiece X x y z (P i)) ∧
      s.biUnion (fun i => physPiece X x y z (P i)) = R.biUnion (physPath x y z) ∪ L := by
  refine ⟨?_, ?_⟩
  · intro i hi j hj hij
    exact h.physPiece_disjoint (hP i hi) (hP j hj) (hdis hi hj hij)
  · have : s.biUnion (fun i => physPiece X x y z (P i)) = physPiece X x y z (s.biUnion P) := by
      unfold physPiece
      rw [biUnion_biUnion]
    rw [this, hU]
    unfold physPiece
    rw [union_biUnion]
    change physPiece X x y z R ∪ physPiece X x y z L = _
    rw [h.physPiece_R, physPiece_of_subset_X hL]

/-- The total incidence of the physical pieces. -/
theorem sum_physPiece_incidentLoad {I : Type*} (h : PathSystem G X R x y z)
    (P : I → Finset (Sym2 V)) (s : Finset I) (hP : ∀ i ∈ s, P i ⊆ X ∪ R)
    (wt : Sym2 V → ℕ) (hwt : ∀ e ∈ R, (∑ i ∈ s, if e ∈ P i then 1 else 0) ≤ wt e) (w : V) :
    ∑ i ∈ s, incidentLoad (physPiece X x y z (P i)) w ≤
      ∑ i ∈ s, incidentLoad (P i) w + 2 * intLoad wt R x y z w := by
  rw [sum_congr rfl fun i hi => h.physPiece_incidentLoad (hP i hi) w, sum_add_distrib,
    ← mul_sum]
  refine Nat.add_le_add_left (Nat.mul_le_mul_left 2 ?_) _
  have hstep : ∀ i ∈ s, (∑ e ∈ P i, if e ∉ X ∧ (w = x e ∨ w = y e ∨ w = z e) then 1 else 0) =
      ∑ e ∈ R, if e ∈ P i ∧ (w = x e ∨ w = y e ∨ w = z e) then 1 else 0 := by
    intro i hi
    rw [← sum_filter, ← sum_filter]
    congr 1
    ext e
    simp only [mem_filter]
    constructor
    · rintro ⟨heP, hnX, hw⟩
      rcases mem_union.mp (hP i hi heP) with hX | hR
      · exact absurd hX hnX
      · exact ⟨hR, heP, hw⟩
    · rintro ⟨hR, heP, hw⟩
      exact ⟨heP, fun hX => disjoint_left.mp h.disjRX hR hX, hw⟩
  rw [sum_congr rfl hstep, sum_comm]
  unfold intLoad
  refine sum_le_sum fun e he => ?_
  by_cases hw : w = x e ∨ w = y e ∨ w = z e
  · simp only [hw, and_true, if_true]
    exact hwt e he
  · simp only [hw, and_false, if_false, sum_const_zero, le_refl]

end PathSystem

end PaddedNoCommon
