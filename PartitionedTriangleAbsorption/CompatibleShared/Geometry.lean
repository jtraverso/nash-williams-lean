/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleShared.Order
public import PartitionedTriangleAbsorption.F0TokenQueries

/-! # Actual-query geometry of the compatible F0 library from anti-edgefulness

For the concrete library `compatB p pV X hX` of the Stage43 compatible producer (charge
correction rebuilt after choosing the compatible labels), the earlier-neighbour set of every
non-root support identity in the rank order roots < hubs < request middles < token vertices
(by gadget index) has one of three shapes:

* empty (hubs, and token vertices without earlier gadget neighbours);
* a single identity;
* two distinct identities whose labels, together with the label of the new identity, form a
  permitted F0 type (request middles: `centre_permitted`; token closing steps:
  `F0TokenQueries.earlier_cases`).

Consequently, from `AntiEdgeful pV F0 G α`, `0 < α` and `3 ≤ |V|`, every legal partial
placement has at least `α |V|` candidates for the next identity (`compatible_geometry`).
Two-root queries use distinctness of the two images, which follows from coappearance
in an actual piece and piecewise injectivity of a legal placement. No supply is claimed for
unpermitted typed patterns.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks UniversalRefiner
open SharedGreedyPort TypedEmbeddingSelection F0FlexibleCompressed

/-- The three admissible shapes of an earlier-neighbour set `N` of a new identity `v`. -/
def EarlierShape {A : Type*} [DecidableEq A] (pA : A → Fin 2) (N : Finset A) (v : A) : Prop :=
  N = ∅ ∨ (∃ u, N = {u}) ∨
    (∃ u₁ u₂, u₁ ≠ u₂ ∧ N = {u₁, u₂} ∧ ({pA u₁, pA u₂, pA v} : Multiset (Fin 2)) ∈ F0)

theorem subset_pair_cases {A : Type*} [DecidableEq A] {N : Finset A} {x y : A}
    (h : N ⊆ {x, y}) : N = ∅ ∨ N = {x} ∨ N = {y} ∨ N = {x, y} := by
  by_cases hx : x ∈ N <;> by_cases hy : y ∈ N
  · right; right; right
    exact Subset.antisymm h (insert_subset hx (singleton_subset_iff.mpr hy))
  · right; left
    refine Subset.antisymm (fun u hu => ?_) (singleton_subset_iff.mpr hx)
    rcases mem_insert.mp (h hu) with rfl | hu'
    · exact mem_singleton_self _
    · rw [mem_singleton] at hu'; subst hu'; exact absurd hu hy
  · right; right; left
    refine Subset.antisymm (fun u hu => ?_) (singleton_subset_iff.mpr hy)
    rcases mem_insert.mp (h hu) with rfl | hu'
    · exact absurd hu hx
    · exact hu'
  · left
    refine eq_empty_of_forall_notMem fun u hu => ?_
    rcases mem_insert.mp (h hu) with rfl | hu'
    · exact hx hu
    · rw [mem_singleton] at hu'; subst hu'; exact hy hu

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {p : ℕ} {X : Finset (Sym2 V)} {hX : ∀ e ∈ X, ¬ e.IsDiag}
  {indices : Finset (RefI V p)}

omit [Fintype V] [DecidableEq V] in
theorem tokV_injective (p : ℕ) (t : Tok (LibIdx (RefU V p))) :
    Function.Injective (tokV (V := V) p t) := by
  intro a b h
  simpa [tokV] using h

theorem tokV_not_root_set (t : Tok (LibIdx (RefU V p))) (k : Fin 8) :
    tokV (V := V) p t k ∉ sharedRoots p := fun h => by
  obtain ⟨v, hv⟩ := mem_sharedRoots.mp h
  exact tokV_not_root v hv

/-- For a token vertex in the support, the earlier neighbours are exactly the images of the
earlier gadget neighbours used in `F0TokenQueries`. -/
theorem earlier_tok {lab : WP (RefU V p) → Fin 2}
    (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {t : Tok (LibIdx (RefU V p))} {k : Fin 8}
    (hvU : tokV p t k ∈ vsupp (libU indices (flexB p lab X hX))) :
    earlier indices (flexB p lab X hX) (sharedRoots p) (sharedRank p) (tokV p t k) =
      (F0TokenQueries.earlier t.sign k).image (tokV p t) := by
  have hrk : ∀ k' : Fin 8, sharedRank p (tokV (V := V) p t k') = 3 + k'.val := fun _ => rfl
  ext u
  constructor
  · intro hu
    have hc := earlier_subset_cand hlib (tokV_not_root_set (p := p) t k) hu
    simp only [candEarlier, mem_image, mem_filter, mem_univ, true_and] at hc
    obtain ⟨k', hk', rfl⟩ := hc
    obtain ⟨-, -, hord⟩ := mem_earlier.mp hu
    have hlt : k'.val < k.val := by
      rcases hord with hroot | hlt
      · exact absurd hroot (tokV_not_root_set (p := p) t k')
      · rw [hrk, hrk] at hlt; omega
    exact mem_image.mpr ⟨k', mem_filter.mpr ⟨mem_univ _, hlt, hk'⟩, rfl⟩
  · intro hu
    obtain ⟨k', hk', rfl⟩ := mem_image.mp hu
    obtain ⟨-, hlt, hk'g⟩ := mem_filter.mp hk'
    obtain ⟨e, he, hve⟩ := mem_vsupp.mp hvU
    obtain ⟨j, hj, -, hcase⟩ := edge_cases_U p lab X hX indices hlib he
    rcases hcase with ⟨e₀, -, h⟩ | ⟨r, -, hr⟩ | ⟨t', htB, ht'⟩
    · exact absurd (mem_sharedRoots.mpr (root_of_mem_map_refEmb (h ▸ hve)))
        (tokV_not_root_set (p := p) t k)
    · rcases vertex_of_mem_pathE hr hve with h | h | h <;> simp [tokV, midV, uV] at h
    · obtain ⟨k'', hk''⟩ := tok_vertex_of_mem_tokE ht' hve
      have htt : t = t' := by simp only [tokV, Sum.inr.injEq, Prod.mk.injEq] at hk''; exact hk''.1
      subst htt
      have hedge : s(tokV p t k', tokV p t k) ∈ libU indices (flexB p lab X hX) :=
        mem_libU.mpr ⟨j, hj, htB (mem_mapE.mpr ⟨s(k', k), hk'g, rfl⟩)⟩
      refine mem_earlier.mpr ⟨mem_vsupp.mpr ⟨_, hedge, Sym2.mem_mk_left _ _⟩, hedge, Or.inr ?_⟩
      rw [hrk, hrk]; omega

/-- **Shapes of the actual queries of the compatible library.** -/
theorem earlier_shape (pV : V → Fin 2)
    (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {v : RefW V p} (hvU : v ∈ vsupp (libU indices (compatB p pV X hX)))
    (hv : v ∉ sharedRoots p) :
    EarlierShape (compatiblePart p pV)
      (earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v) v := by
  have hsub := earlier_subset_cand (lab := compatibleMid p pV) hlib hv
  rcases v with (x | r) | ⟨t, k⟩
  · left
    exact subset_empty.mp (by simpa [candEarlier] using hsub)
  · simp only [candEarlier] at hsub
    rcases subset_pair_cases hsub with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨_, h⟩)
    · exact Or.inr (Or.inl ⟨_, h⟩)
    · by_cases hxy : uV p (rtS p r).1 = uV (V := V) p (rtS p r).2
      · rw [hxy, insert_eq_of_mem (mem_singleton_self _)] at h
        exact Or.inr (Or.inl ⟨_, h⟩)
      · exact Or.inr (Or.inr ⟨_, _, hxy, h, F0RequestLabels.centre_permitted _ _⟩)
  · rw [earlier_tok hlib hvU]
    rcases F0TokenQueries.earlier_cases t.sign k with h | ⟨i, h⟩ | ⟨i, l, hil, h, ht⟩
    · left; rw [h, image_empty]
    · right; left; exact ⟨tokV p t i, by rw [h, image_singleton]⟩
    · right; right
      refine ⟨tokV p t i, tokV p t l, fun h' => hil (tokV_injective p t h'), ?_, ht⟩
      rw [h, image_insert, image_singleton]

/-- **Actual-query geometry of the compatible library, derived from anti-edgefulness.**
For every legal partial placement `g` (with any root map `r`) of a set `P` containing the
earlier neighbours of a non-placed support identity `v`, at least `α |V|` host vertices of
the part of `v` are adjacent to all images of those earlier neighbours. -/
theorem compatible_geometry (pV : V → Fin 2)
    (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset (Sym2 V)) (q : ℕ) (r : RefW V p → V)
    (alpha : ℝ) (ha : 0 < alpha) (hn : 3 ≤ Fintype.card V)
    (hanti : AntiEdgeful pV F0 G alpha) :
    ∀ (P : Finset (RefW V p)) (g : RefW V p → V) (v : RefW V p),
      Legal indices (compatB p pV X hX) (sharedRoots p) r (compatiblePart p pV) pV G F X q P g →
      v ∈ vsupp (libU indices (compatB p pV X hX)) → v ∉ P →
      earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v ⊆ P →
      alpha * Fintype.card V ≤ (typedNeighbours pV G
        ((earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v).image g)
        (compatiblePart p pV v)).card := by
  intro P g v hL hvU hvP hNP
  have hparts := F0PatternSupply.parts_present pV G alpha ha hn hanti
  have hvR : v ∉ sharedRoots p := fun h => hvP (hL.roots_sub h)
  rcases earlier_shape pV hlib hvU hvR with h | ⟨u, h⟩ | ⟨u₁, u₂, hne, h, ht⟩
  · rw [h, image_empty]
    exact F0PatternSupply.empty_supply pV G alpha hanti hparts _
  · rw [h, image_singleton]
    exact F0PatternSupply.single_supply pV G alpha hanti hparts _ _
  · have h₁ : u₁ ∈ earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v := by
      rw [h]; exact mem_insert_self _ _
    have h₂ : u₂ ∈ earlier indices (compatB p pV X hX) (sharedRoots p) (sharedRank p) v := by
      rw [h]; exact mem_insert_of_mem (mem_singleton_self _)
    obtain ⟨j, hj, hu₁j, hu₂j⟩ := earlier_coappear hlib hvU hvR h₁ h₂
    have hg : g u₁ ≠ g u₂ := fun hg => hne (hL.inj_piece j hj
      (mem_coe.mpr (mem_inter.mpr ⟨hu₁j, hNP h₁⟩))
      (mem_coe.mpr (mem_inter.mpr ⟨hu₂j, hNP h₂⟩)) hg)
    have htype : ({pV (g u₁), pV (g u₂), compatiblePart p pV v} : Multiset (Fin 2)) ∈ F0 := by
      rw [hL.part u₁ (hNP h₁), hL.part u₂ (hNP h₂)]
      exact ht
    rw [h, image_insert, image_singleton]
    exact F0PatternSupply.pair_supply pV G alpha hanti _ _ hg _ htype

end PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared
