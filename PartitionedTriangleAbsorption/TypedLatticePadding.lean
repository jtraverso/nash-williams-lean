/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import PartitionedTriangleAbsorption.AntiEdgeSelection
public import Mathlib.Tactic.Linarith

/-! # Integral (signed) global coefficients suffice for private absorbers

The coloured-hub template (`MATHEMATICAL_COLOURED_HUB_PRIVATE_TEMPLATE_NEXT_20261007.md`,
not formalized) asks for an even piece whose global edge vector is a *nonnegative* integer
combination of type edge vectors. This file shows that the nonnegativity can always be
bought: add vertex-disjoint fresh typed triangles, one for each unit of negative
coefficient. The padded piece has nonnegative coefficients, its padding is decomposable and
meets no original vertex, and any absorber of the padded piece, together with the padding,
absorbs the original piece.

So a refiner piece only needs even degrees and an *integral* global coefficient vector
(equivalently, by `TypedDivisibilityCollapse`, integral divisibility), provided the
nonnegative template is available. The template itself remains an explicit hypothesis.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedLatticePadding

open Finset AntiEdgeSelection

variable {t : ℕ}

/-- **Absorber transfer.** If `Q` is decomposable and disjoint from `P`, then an absorber
`A'` of `P ∪ Q` gives the absorber `A' ∪ Q` of `P`. -/
theorem absorber_of_padding {W : Type*} [DecidableEq W] {p : W → Fin t}
    {F : Finset (Multiset (Fin t))} {P Q A' : Finset (Sym2 W)}
    (hPQ : Disjoint P Q) (hQ : HasDecomp p F Q) (hdis : Disjoint A' (P ∪ Q))
    (hA' : HasDecomp p F A') (hA'PQ : HasDecomp p F (A' ∪ (P ∪ Q))) :
    Disjoint (A' ∪ Q) P ∧ HasDecomp p F (A' ∪ Q) ∧ HasDecomp p F ((A' ∪ Q) ∪ P) := by
  refine ⟨disjoint_union_left.mpr ⟨hdis.mono_right subset_union_left, hPQ.symm⟩,
    hA'.union hQ (hdis.mono_right subset_union_right), ?_⟩
  have e : (A' ∪ Q) ∪ P = A' ∪ (P ∪ Q) := by
    ext e; simp only [mem_union]; tauto
  rw [e]; exact hA'PQ

/-! ### Fresh typed triangles -/

variable {W T : Type*} [DecidableEq W] [Fintype T] [DecidableEq T]

/-- Original vertices together with three fresh vertices for each padding index. -/
abbrev Ext (W T : Type*) := W ⊕ (T × Fin 3)

/-- The copy of an original edge set. -/
def liftE (P : Finset (Sym2 W)) : Finset (Sym2 (Ext W T)) := P.image (Sym2.map Sum.inl)

/-- The fresh triangle with index `x`. -/
def freshTri (x : T) : Finset (Ext W T) :=
  {Sum.inr (x, 0), Sum.inr (x, 1), Sum.inr (x, 2)}

/-- All padding edges. -/
def padding : Finset (Sym2 (Ext W T)) :=
  univ.biUnion fun x => triEdges (freshTri (W := W) x)

/-- The extended partition: fresh vertex `(x, i)` gets part `σ x i`. -/
def extPart (p : W → Fin t) (σ : T → Fin 3 → Fin t) : Ext W T → Fin t :=
  Sum.elim p fun z => σ z.1 z.2

/-- The padding type of index `x`. -/
def padType (σ : T → Fin 3 → Fin t) (x : T) : Multiset (Fin t) := {σ x 0, σ x 1, σ x 2}

omit [DecidableEq W] [Fintype T] [DecidableEq T] in
theorem freshTri_ne {x : T} :
    (Sum.inr (x, 0) : Ext W T) ≠ Sum.inr (x, 1) ∧ (Sum.inr (x, 0) : Ext W T) ≠ Sum.inr (x, 2) ∧
      (Sum.inr (x, 1) : Ext W T) ≠ Sum.inr (x, 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

omit [Fintype T] in
theorem freshTri_card (x : T) : (freshTri (W := W) x).card = 3 := by
  obtain ⟨h1, h2, h3⟩ := freshTri_ne (W := W) (x := x)
  rw [freshTri, card_insert_of_notMem (by simp [h1, h2]), card_pair h3]

omit [Fintype T] in
theorem mem_triEdges_freshTri {x : T} {e : Sym2 (Ext W T)}
    (he : e ∈ triEdges (freshTri (W := W) x)) : ∀ z ∈ e, z ∈ freshTri (W := W) x := by
  rw [triEdges, mem_filter, mem_sym2_iff] at he
  exact he.1

omit [Fintype T] in
theorem freshTri_disjoint {x y : T} (hxy : x ≠ y) :
    Disjoint (freshTri (W := W) x) (freshTri (W := W) y) := by
  rw [disjoint_left]
  intro z hz hz'
  simp only [freshTri, mem_insert, mem_singleton] at hz hz'
  rcases hz with rfl | rfl | rfl <;> rcases hz' with h | h | h <;> simp_all

omit [Fintype T] in
theorem triEdges_freshTri_disjoint {x y : T} (hxy : x ≠ y) :
    Disjoint (triEdges (freshTri (W := W) x)) (triEdges (freshTri (W := W) y)) := by
  rw [disjoint_left]
  intro e he he'
  induction e using Sym2.ind with
  | _ a b =>
    have ha := mem_triEdges_freshTri he a (Sym2.mem_mk_left a b)
    have ha' := mem_triEdges_freshTri he' a (Sym2.mem_mk_left a b)
    exact disjoint_left.mp (freshTri_disjoint hxy) ha ha'

theorem padding_hasDecomp {F : Finset (Multiset (Fin t))} (p : W → Fin t)
    (σ : T → Fin 3 → Fin t) (hσ : ∀ x, padType σ x ∈ F) :
    HasDecomp (extPart p σ) F (padding (W := W) (T := T)) := by
  refine ⟨univ.image (freshTri (W := W)), ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨x, -, rfl⟩ := mem_image.mp hs
    refine ⟨freshTri_card x, ?_⟩
    obtain ⟨h1, h2, h3⟩ := freshTri_ne (W := W) (x := x)
    rw [freshTri, map_three _ h1 h2 h3]
    exact hσ x
  · intro s hs s' hs' hss'
    obtain ⟨x, -, rfl⟩ := mem_image.mp hs
    obtain ⟨y, -, rfl⟩ := mem_image.mp hs'
    have hxy : x ≠ y := fun h => hss' (h ▸ rfl)
    exact triEdges_freshTri_disjoint hxy
  · rw [padding, image_biUnion]

theorem padding_disjoint_lift (P : Finset (Sym2 W)) :
    Disjoint (liftE (T := T) P) (padding (W := W) (T := T)) := by
  rw [disjoint_left]
  intro e he he'
  obtain ⟨a, -, rfl⟩ := mem_image.mp he
  obtain ⟨x, -, hx⟩ := mem_biUnion.mp he'
  induction a using Sym2.ind with
  | _ u v =>
    have := mem_triEdges_freshTri hx (Sum.inl u) (by simp)
    simp [freshTri] at this

theorem padding_avoids_original (w : W) :
    incidentLoad (padding (W := W) (T := T)) (Sum.inl w) = 0 := by
  rw [incidentLoad, card_eq_zero, filter_eq_empty_iff]
  intro e he hw
  obtain ⟨x, -, hx⟩ := mem_biUnion.mp he
  have := mem_triEdges_freshTri hx _ hw
  simp [freshTri] at this

theorem padding_card : (padding (W := W) (T := T)).card = 3 * Fintype.card T := by
  rw [padding, card_biUnion fun x _ y _ hxy => triEdges_freshTri_disjoint hxy]
  have : ∀ x : T, (triEdges (freshTri (W := W) x)).card = 3 := by
    intro x
    obtain ⟨h1, h2, h3⟩ := freshTri_ne (W := W) (x := x)
    rw [freshTri, PartitionedTriangleAbsorption.triEdges_three h1 h2 h3]
    have n1 : s(Sum.inr (x, 0), Sum.inr (x, 1)) ≠ (s(Sum.inr (x, 0), Sum.inr (x, 2)) :
        Sym2 (Ext W T)) := by simp
    have n2 : s(Sum.inr (x, 0), Sum.inr (x, 1)) ≠ (s(Sum.inr (x, 1), Sum.inr (x, 2)) :
        Sym2 (Ext W T)) := by simp
    have n3 : s(Sum.inr (x, 0), Sum.inr (x, 2)) ≠ (s(Sum.inr (x, 1), Sum.inr (x, 2)) :
        Sym2 (Ext W T)) := by simp
    rw [card_insert_of_notMem (by simp [n1, n2]), card_pair n3]
  rw [sum_congr rfl fun x _ => this x, sum_const, card_univ, smul_eq_mul, mul_comm]

omit [Fintype T] in
theorem edgeVec_liftE (p : W → Fin t) (σ : T → Fin 3 → Fin t) (P : Finset (Sym2 W)) :
    edgeVec (extPart p σ) (liftE (T := T) P) = edgeVec p P := by
  rw [edgeVec, liftE, sum_image fun a _ b _ h => Sym2.map.injective Sum.inl_injective h]
  refine sum_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ a b => rfl

theorem edgeVec_padding (p : W → Fin t) (σ : T → Fin 3 → Fin t) :
    edgeVec (extPart p σ) (padding (W := W) (T := T)) =
      ∑ x, typeEdgeVec (padType σ x) := by
  rw [edgeVec, padding, sum_biUnion fun x _ y _ hxy => triEdges_freshTri_disjoint hxy]
  refine sum_congr rfl fun x _ => ?_
  rw [← edgeVec, edgeVec_triEdges _ (freshTri_card x), triType]
  obtain ⟨h1, h2, h3⟩ := freshTri_ne (W := W) (x := x)
  rw [freshTri, map_three _ h1 h2 h3]
  rfl

/-- **Padding.** If `P` has integral global coefficients `c`, and the padding indices of
type `τ` number exactly the negative part of `c τ`, then the padded piece has the
nonnegative coefficients `max (c τ) 0`. -/
theorem padded_coefficients {F : Finset (Multiset (Fin t))} (p : W → Fin t)
    (σ : T → Fin 3 → Fin t) (hσ : ∀ x, padType σ x ∈ F) (P : Finset (Sym2 W))
    (c : Multiset (Fin t) → ℤ) (hc : edgeVec p P = ∑ τ ∈ F, c τ • typeEdgeVec τ)
    (hcount : ∀ τ ∈ F, ((univ.filter fun x => padType σ x = τ).card : ℤ) = max (-c τ) 0) :
    edgeVec (extPart p σ) (liftE P ∪ padding (W := W) (T := T)) =
      ∑ τ ∈ F, (max (c τ) 0) • typeEdgeVec τ := by
  rw [edgeVec_union _ (padding_disjoint_lift P), edgeVec_liftE, edgeVec_padding, hc]
  rw [← sum_fiberwise_of_maps_to (g := padType σ) (t := F) (fun x _ => hσ x)]
  rw [← sum_add_distrib]
  refine sum_congr rfl fun τ hτ => ?_
  have hfib : ∑ x ∈ univ.filter (fun x => padType σ x = τ), typeEdgeVec (padType σ x) =
      ((univ.filter fun x => padType σ x = τ).card : ℤ) • typeEdgeVec τ := by
    rw [natCast_zsmul, ← sum_const]
    exact sum_congr rfl fun x hx => by rw [(mem_filter.mp hx).2]
  rw [hfib, hcount τ hτ, ← add_smul]
  congr 1
  omega

/-- **Lattice pieces suffice.** Let `P` have integral global coefficients. Pad it as above.
Any absorber `A'` of the padded piece (which has nonnegative coefficients and the same
degrees at original vertices) yields the absorber `A' ∪ padding` of the copy of `P`; the
padding has `3·|T|` edges and meets no original vertex. -/
theorem absorber_of_lattice_piece {F : Finset (Multiset (Fin t))} (p : W → Fin t)
    (σ : T → Fin 3 → Fin t) (hσ : ∀ x, padType σ x ∈ F) (P : Finset (Sym2 W))
    (A' : Finset (Sym2 (Ext W T)))
    (hdis : Disjoint A' (liftE P ∪ padding (W := W) (T := T)))
    (hA' : HasDecomp (extPart p σ) F A')
    (hA'P : HasDecomp (extPart p σ) F (A' ∪ (liftE P ∪ padding (W := W) (T := T)))) :
    Disjoint (A' ∪ padding) (liftE P) ∧ HasDecomp (extPart p σ) F (A' ∪ padding) ∧
      HasDecomp (extPart p σ) F ((A' ∪ padding) ∪ liftE P) :=
  absorber_of_padding (padding_disjoint_lift P) (padding_hasDecomp p σ hσ) hdis hA' hA'P

end PartitionedTriangleAbsorption.TypedLatticePadding
