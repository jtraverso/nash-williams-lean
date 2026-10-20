/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBasic
public import Mathlib.Tactic

/-! # The physical one-round nibble model (deterministic part)

Triangles are distinct three-element vertex sets `tri i`, indexed by the
coordinates `i : Fin m` of the Bernoulli cube. For a coin assignment `ω`:

* `retainedSet ω` : triangles whose coin is `true`;
* `touched ω` (`Q`) : all edges of retained triangles;
* `packing ω` (`P`) : retained triangles sharing no edge with another retained one;
* `untouched B ω` (`B' = B \ Q`) and `waste ω` (`W = Q \ E(P)`).

We prove the exact residual identity `B \ E(P) = B' ⊔ W`, that `P` is an
edge-disjoint packing, and the two deterministic star inequalities
`d_{E(P)}(v) ≥ 2(R - Z - 2F)` and `d_W(v) ≤ 2Z + 4F`.
-/

/-
New isolated module for the 2026-10-12 task.
Source proof: PartitionedTriangleAbsorption/Nibble/Model.lean.
Original SHA256: af471dd3388e609b8a005e4c22926697158f08f50d7bc4bcc57081f398274be5.
Only namespace/import isolation and explicitly indicated elementary estimates
are changed; the original file is not modified.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble

open Finset

variable {V : Type*} [DecidableEq V]

/-- The edges of a vertex set (for a triangle: its three edges). -/
def triEdges (T : Finset V) : Finset (Sym2 V) := T.sym2.filter (fun e => ¬ e.IsDiag)

theorem mem_triEdges {T : Finset V} {x y : V} :
    s(x, y) ∈ triEdges T ↔ x ∈ T ∧ y ∈ T ∧ x ≠ y := by
  simp [triEdges, and_assoc]

/-- The edges at `v` in an edge set. -/
def star (S : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) := S.filter (fun e => v ∈ e)

/-- A finite family of distinct physical triangles. -/
structure TriSystem (V : Type*) [DecidableEq V] (m : ℕ) where
  tri : Fin m → Finset V
  card_tri : ∀ i, (tri i).card = 3
  tri_inj : Function.Injective tri

variable {m : ℕ} (S : TriSystem V m)

namespace TriSystem

/-- Two triangles share a physical edge. -/
def Shares (i j : Fin m) : Prop := ¬ Disjoint (triEdges (S.tri i)) (triEdges (S.tri j))

instance (i j : Fin m) : Decidable (S.Shares i j) := by unfold Shares; infer_instance

end TriSystem

def retainedSet (ω : Fin m → Bool) : Finset (Fin m) := univ.filter (fun i => ω i = true)

namespace TriSystem

/-- `Q`: every edge touched by a retained triangle. -/
def touched (ω : Fin m → Bool) : Finset (Sym2 V) :=
  (retainedSet ω).biUnion (fun i => triEdges (S.tri i))

/-- Retained and sharing no edge with any other retained triangle. -/
def Isolated (ω : Fin m → Bool) (i : Fin m) : Prop :=
  ω i = true ∧ ∀ j, j ≠ i → ω j = true → ¬ S.Shares i j

instance (ω : Fin m → Bool) (i : Fin m) : Decidable (S.Isolated ω i) := by
  unfold Isolated; infer_instance

/-- `P`: the isolated retained triangles. -/
def packing (ω : Fin m → Bool) : Finset (Fin m) := univ.filter (S.Isolated ω)

/-- `E(P)`. -/
def packEdges (ω : Fin m → Bool) : Finset (Sym2 V) :=
  (S.packing ω).biUnion (fun i => triEdges (S.tri i))

/-- `B' = B \ Q`. -/
def untouched (B : Finset (Sym2 V)) (ω : Fin m → Bool) : Finset (Sym2 V) := B \ S.touched ω

/-- `W = Q \ E(P)`. -/
def waste (ω : Fin m → Bool) : Finset (Sym2 V) := S.touched ω \ S.packEdges ω

theorem packing_subset_retained (ω : Fin m → Bool) : S.packing ω ⊆ retainedSet ω := by
  intro i hi
  simp only [packing, mem_filter, mem_univ, true_and] at hi
  simp [retainedSet, hi.1]

theorem packEdges_subset_touched (ω : Fin m → Bool) : S.packEdges ω ⊆ S.touched ω :=
  biUnion_subset_biUnion_of_subset_left _ (S.packing_subset_retained ω)

/-- The packing is edge-disjoint. -/
theorem packing_edge_disjoint (ω : Fin m → Bool) {i j : Fin m}
    (hi : i ∈ S.packing ω) (hj : j ∈ S.packing ω) (hij : i ≠ j) :
    Disjoint (triEdges (S.tri i)) (triEdges (S.tri j)) := by
  simp only [packing, mem_filter, mem_univ, true_and] at hi hj
  have := hi.2 j (Ne.symm hij) hj.1
  simpa [Shares] using this

/-- Exact residual identity `B \ E(P) = B' ∪ W` with `B' ∩ W = ∅`, provided every
triangle edge is active. -/
theorem residual_identity (B : Finset (Sym2 V)) (hB : ∀ i, triEdges (S.tri i) ⊆ B)
    (ω : Fin m → Bool) :
    B \ S.packEdges ω = S.untouched B ω ∪ S.waste ω ∧
      Disjoint (S.untouched B ω) (S.waste ω) := by
  have hQB : S.touched ω ⊆ B := biUnion_subset.mpr fun i _ => hB i
  have hPQ := S.packEdges_subset_touched ω
  constructor
  · ext e
    simp only [untouched, waste, mem_sdiff, mem_union]
    constructor
    · rintro ⟨heB, heP⟩
      by_cases heQ : e ∈ S.touched ω
      · exact Or.inr ⟨heQ, heP⟩
      · exact Or.inl ⟨heB, heQ⟩
    · rintro (⟨heB, heQ⟩ | ⟨heQ, heP⟩)
      · exact ⟨heB, fun h => heQ (hPQ h)⟩
      · exact ⟨hQB heQ, heP⟩
  · rw [Finset.disjoint_left]
    intro e h1 h2
    simp only [untouched, waste, mem_sdiff] at h1 h2
    exact h1.2 h2.1

/-! ## Star statistics -/

/-- `A_v`: triangles through `v`. -/
def through (v : V) : Finset (Fin m) := univ.filter (fun i => v ∈ S.tri i)

/-- `R_v`: retained triangles through `v`. -/
def retainedThrough (ω : Fin m → Bool) (v : V) : Finset (Fin m) :=
  (S.through v).filter (fun i => ω i = true)

/-- Triangles blocked by a retained triangle not through `v`. -/
def Blocked (ω : Fin m → Bool) (v : V) (i : Fin m) : Prop :=
  ∃ j, v ∉ S.tri j ∧ ω j = true ∧ S.Shares i j

instance (ω : Fin m → Bool) (v : V) (i : Fin m) : Decidable (S.Blocked ω v i) := by
  unfold Blocked; infer_instance

/-- `Z_v`: retained triangles through `v` that are blocked from outside. -/
def blockedRetained (ω : Fin m → Bool) (v : V) : Finset (Fin m) :=
  (S.retainedThrough ω v).filter (S.Blocked ω v)

/-- Link degree `D_a`: retained triangles through `v` and `a`. -/
def linkDeg (ω : Fin m → Bool) (v a : V) : ℕ :=
  ((S.retainedThrough ω v).filter (fun i => a ∈ S.tri i)).card

/-- `F_v = ∑_{a ≠ v} C(D_a, 2)`. -/
def conflicts [Fintype V] (ω : Fin m → Bool) (v : V) : ℕ :=
  ∑ a ∈ univ.erase v, (S.linkDeg ω v a).choose 2

/-- Two distinct triangles through `v` can only share an edge at `v`. -/
theorem shared_edge_contains_v {i j : Fin m} {v : V} (hvi : v ∈ S.tri i) (hvj : v ∈ S.tri j)
    (hij : i ≠ j) {e : Sym2 V} (hei : e ∈ triEdges (S.tri i)) (hej : e ∈ triEdges (S.tri j)) :
    v ∈ e := by
  by_contra hve
  induction e using Sym2.ind with
  | _ x y =>
  rw [mem_triEdges] at hei hej
  have hxv : x ≠ v := fun h => hve (h ▸ Sym2.mem_mk_left x y)
  have hyv : y ≠ v := fun h => hve (h ▸ Sym2.mem_mk_right x y)
  have hsub : ({v, x, y} : Finset V) ⊆ S.tri i := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> tauto
  have hsubj : ({v, x, y} : Finset V) ⊆ S.tri j := by
    intro z hz
    simp only [mem_insert, mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> tauto
  have hcard : ({v, x, y} : Finset V).card = 3 := by
    rw [card_insert_of_notMem (by simp [hxv.symm, hyv.symm]),
      card_pair hei.2.2]
  have h1 := eq_of_subset_of_card_le hsub (by rw [S.card_tri, hcard])
  have h2 := eq_of_subset_of_card_le hsubj (by rw [S.card_tri, hcard])
  exact hij (S.tri_inj (h1.symm.trans h2))

/-- Retained triangles through `v` that are not isolated are blocked from outside,
or lie at a link vertex of link degree at least two. -/
theorem nonisolated_subset [Fintype V] (ω : Fin m → Bool) (v : V) :
    (S.retainedThrough ω v).filter (fun i => ¬ S.Isolated ω i) ⊆
      S.blockedRetained ω v ∪ (univ.erase v).biUnion (fun a =>
        if 2 ≤ S.linkDeg ω v a then
          (S.retainedThrough ω v).filter (fun i => a ∈ S.tri i) else ∅) := by
  intro i hi
  simp only [mem_filter, retainedThrough, through, mem_univ, true_and] at hi
  obtain ⟨⟨hvi, hωi⟩, hnot⟩ := hi
  simp only [Isolated, hωi, true_and, not_forall, not_not] at hnot
  obtain ⟨j, hji, hωj, hsh⟩ := hnot
  by_cases hvj : v ∈ S.tri j
  · apply mem_union_right
    obtain ⟨e, hei, hej⟩ := Finset.not_disjoint_iff.mp hsh
    have hve := S.shared_edge_contains_v hvi hvj (Ne.symm hji) hei hej
    obtain ⟨a, rfl⟩ := (Sym2.mem_iff_exists).mp hve
    rw [mem_triEdges] at hei hej
    simp only [mem_biUnion, mem_erase, mem_univ, and_true]
    refine ⟨a, hei.2.2.symm, ?_⟩
    have hge : 2 ≤ S.linkDeg ω v a := by
      unfold linkDeg
      have : ({i, j} : Finset (Fin m)) ⊆
          (S.retainedThrough ω v).filter (fun k => a ∈ S.tri k) := by
        intro k hk
        simp only [mem_insert, mem_singleton] at hk
        rcases hk with rfl | rfl <;>
          simp [retainedThrough, through, *]
      calc 2 = ({i, j} : Finset (Fin m)).card := (card_pair (Ne.symm hji)).symm
        _ ≤ _ := card_le_card this
    rw [ite_eq_left hge]
    simp [retainedThrough, through, hvi, hωi, hei.2.1]
  · apply mem_union_left
    simp only [blockedRetained, retainedThrough, through, mem_filter, mem_univ, true_and]
    exact ⟨⟨hvi, hωi⟩, j, hvj, hωj, hsh⟩

theorem card_nonisolated_le [Fintype V] (ω : Fin m → Bool) (v : V) :
    ((S.retainedThrough ω v).filter (fun i => ¬ S.Isolated ω i)).card ≤
      (S.blockedRetained ω v).card + 2 * S.conflicts ω v := by
  refine (card_le_card (S.nonisolated_subset ω v)).trans ?_
  refine (card_union_le _ _).trans (Nat.add_le_add_left ?_ _)
  refine card_biUnion_le.trans ?_
  unfold conflicts
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  split_ifs with h
  · change S.linkDeg ω v a ≤ _
    rw [Nat.choose_two_right]
    have := Nat.div_mul_cancel (Nat.even_mul_pred_self (S.linkDeg ω v a)).two_dvd
    have h2 : S.linkDeg ω v a ≤ S.linkDeg ω v a * (S.linkDeg ω v a - 1) := by
      calc S.linkDeg ω v a = S.linkDeg ω v a * 1 := (mul_one _).symm
        _ ≤ _ := Nat.mul_le_mul_left _ (by omega)
    omega
  · simp

/-- A triangle through `v` has exactly two edges at `v`. -/
theorem card_star_triEdges {i : Fin m} {v : V} (hvi : v ∈ S.tri i) :
    (star (triEdges (S.tri i)) v).card = 2 := by
  have : star (triEdges (S.tri i)) v = ((S.tri i).erase v).image (fun a => s(v, a)) := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
    simp only [star, mem_filter, mem_triEdges, mem_image, mem_erase, Sym2.mem_iff]
    constructor
    · rintro ⟨⟨ha, hb, hab⟩, rfl | rfl⟩
      · exact ⟨b, ⟨hab.symm, hb⟩, rfl⟩
      · exact ⟨a, ⟨hab, ha⟩, Sym2.eq_swap⟩
    · rintro ⟨c, ⟨hcv, hc⟩, he⟩
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨⟨hvi, hc, Ne.symm hcv⟩, Or.inl rfl⟩
      · exact ⟨⟨hc, hvi, hcv⟩, Or.inr rfl⟩
  rw [this, card_image_of_injective _ (fun a b h => Sym2.congr_right.mp h), card_erase_of_mem hvi,
    S.card_tri]

theorem star_triEdges_eq_empty {i : Fin m} {v : V} (hvi : v ∉ S.tri i) :
    star (triEdges (S.tri i)) v = ∅ := by
  ext e
  induction e using Sym2.ind with
  | _ a b =>
  simp only [star, mem_filter, mem_triEdges, Sym2.mem_iff, notMem_empty, iff_false]
  rintro ⟨⟨ha, hb, _⟩, rfl | rfl⟩ <;> contradiction

theorem star_biUnion (s : Finset (Fin m)) (v : V) :
    star (s.biUnion fun i => triEdges (S.tri i)) v =
      (s.filter fun i => v ∈ S.tri i).biUnion fun i => star (triEdges (S.tri i)) v := by
  ext e
  simp only [star, mem_filter, mem_biUnion]
  constructor
  · rintro ⟨⟨i, hi, he⟩, hv⟩
    refine ⟨i, ⟨hi, ?_⟩, he, hv⟩
    by_contra h
    have := S.star_triEdges_eq_empty h
    have hmem : e ∈ star (triEdges (S.tri i)) v := mem_filter.mpr ⟨he, hv⟩
    rw [this] at hmem
    simp at hmem
  · rintro ⟨i, ⟨hi, _⟩, he, hv⟩
    exact ⟨⟨i, hi, he⟩, hv⟩

/-- `d_{E(P)}(v) = 2 |P ∩ A_v|`. -/
theorem card_star_packEdges (ω : Fin m → Bool) (v : V) :
    (star (S.packEdges ω) v).card = 2 * ((S.packing ω).filter fun i => v ∈ S.tri i).card := by
  unfold packEdges
  rw [S.star_biUnion, card_biUnion]
  · rw [sum_congr rfl (fun i hi => S.card_star_triEdges (mem_filter.mp hi).2), sum_const,
      smul_eq_mul, mul_comm]
  · intro i hi j hj hij
    have hd := S.packing_edge_disjoint ω (mem_filter.mp hi).1 (mem_filter.mp hj).1 hij
    exact Finset.disjoint_of_subset_left (filter_subset _ _)
      (Finset.disjoint_of_subset_right (filter_subset _ _) hd)

theorem packing_through_eq (ω : Fin m → Bool) (v : V) :
    (S.packing ω).filter (fun i => v ∈ S.tri i) =
      (S.retainedThrough ω v).filter (fun i => S.Isolated ω i) := by
  ext i
  simp only [packing, retainedThrough, through, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hi, hv⟩
    exact ⟨⟨hv, hi.1⟩, hi⟩
  · rintro ⟨⟨hv, _⟩, hi⟩
    exact ⟨hi, hv⟩

/-- Deterministic progress inequality `R ≤ |P ∩ A_v| + Z + 2F`, i.e.
`d_{E(P)}(v) ≥ 2(R - Z - 2F)`. -/
theorem progress_inequality [Fintype V] (ω : Fin m → Bool) (v : V) :
    (S.retainedThrough ω v).card ≤
      (star (S.packEdges ω) v).card / 2 + (S.blockedRetained ω v).card +
        2 * S.conflicts ω v := by
  rw [S.card_star_packEdges, Nat.mul_div_cancel_left _ (by norm_num), S.packing_through_eq]
  have h := (S.retainedThrough ω v).card_filter_add_card_filter_not
    (fun i => S.Isolated ω i)
  have := S.card_nonisolated_le ω v
  omega

/-- Deterministic waste inequality `d_W(v) ≤ 2Z + 4F`. -/
theorem waste_inequality [Fintype V] (ω : Fin m → Bool) (v : V) :
    (star (S.waste ω) v).card ≤ 2 * (S.blockedRetained ω v).card + 4 * S.conflicts ω v := by
  have hsub : star (S.waste ω) v ⊆
      ((S.retainedThrough ω v).filter (fun i => ¬ S.Isolated ω i)).biUnion
        (fun i => star (triEdges (S.tri i)) v) := by
    intro e he
    simp only [star, waste, touched, mem_filter, mem_sdiff, mem_biUnion] at he
    obtain ⟨⟨⟨i, hi, hei⟩, heP⟩, hv⟩ := he
    have hvi : v ∈ S.tri i := by
      by_contra h
      have := S.star_triEdges_eq_empty h
      have hmem : e ∈ star (triEdges (S.tri i)) v := mem_filter.mpr ⟨hei, hv⟩
      rw [this] at hmem; simp at hmem
    have hni : ¬ S.Isolated ω i := by
      intro hiso
      apply heP
      simp only [packEdges, mem_biUnion]
      exact ⟨i, by simp [packing, hiso], hei⟩
    simp only [mem_biUnion, mem_filter, retainedThrough, through, mem_univ, true_and]
    simp only [retainedSet, mem_filter, mem_univ, true_and] at hi
    exact ⟨i, ⟨⟨hvi, hi⟩, hni⟩, mem_filter.mpr ⟨hei, hv⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans ?_)
  rw [sum_congr rfl (fun i hi => S.card_star_triEdges
    (by simp only [mem_filter, retainedThrough, through, mem_univ, true_and] at hi
        exact hi.1.1))]
  rw [sum_const, smul_eq_mul]
  have := S.card_nonisolated_le ω v
  omega

end TriSystem

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble
