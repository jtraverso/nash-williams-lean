/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleShared.Structure

/-! # The F0 order: roots, hubs, request middles, token vertices

For the concrete library (restricted to its finite active support through `vsupp`):

* `roots_edge`: every root–root library edge is a lifted edge of the physical reserve `X`;
* `rank_ne`: distinct adjacent non-root identities have different ranks;
* `earlier_card_le_two`: every non-root support identity has at most two earlier neighbours;
* `earlier_coappear`: any two distinct earlier neighbours coappear in an actual piece.

Hubs have no earlier neighbours, a request middle has at most its two path endpoints,
and a token vertex has at most its two earlier gadget neighbours.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks UniversalRefiner
open SharedGreedyPort

variable {V : Type*} [Fintype V] [DecidableEq V]

section Library

variable (p : ℕ) (lab : WP (RefU V p) → Fin 2) (X : Finset (Sym2 V)) (hX : ∀ e ∈ X, ¬ e.IsDiag)
  (indices : Finset (RefI V p))

/-- Library-edge classification, on the edge union. -/
theorem edge_cases_U (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {e : Sym2 (RefW V p)} (he : e ∈ libU indices (flexB p lab X hX)) :
    ∃ j ∈ indices, e ∈ flexB p lab X hX j ∧
      ((∃ e₀ ∈ X, e = Sym2.map (refEmb p) e₀) ∨
        (∃ r, pathE p r ⊆ flexB p lab X hX j ∧ e ∈ pathE p r) ∨
        (∃ t, tokE t ⊆ flexB p lab X hX j ∧ e ∈ tokE t)) := by
  obtain ⟨j, hj, hej⟩ := mem_libU.mp he
  exact ⟨j, hj, hej, edge_cases p lab X hX (fun i hi => hlib i (hi ▸ hj)) hej⟩

end Library

omit [Fintype V] [DecidableEq V] in
theorem midV_not_root {p : ℕ} {r : Req (RefU V p)} (v : V) : refEmb p v ≠ midV p r := by
  simp [refEmb]

omit [Fintype V] [DecidableEq V] in
theorem tokV_not_root {p : ℕ} {t : Tok (LibIdx (RefU V p))} {k : Fin 8} (v : V) :
    refEmb p v ≠ tokV p t k := by
  simp [refEmb]

omit [Fintype V] [DecidableEq V] in
theorem hub_not_root {p : ℕ} {i : Fin (2 ^ (p + 1))} (v : V) :
    refEmb p v ≠ uV p (Sum.inr i) := by
  simp [refEmb]

theorem vertex_of_mem_pathE {p : ℕ} {r : Req (RefU V p)} {e : Sym2 (RefW V p)}
    (he : e ∈ pathE p r) {w : RefW V p} (hw : w ∈ e) :
    w = midV p r ∨ w = uV p (rtS p r).1 ∨ w = uV p (rtS p r).2 := by
  simp only [pathE, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl <;> rcases Sym2.mem_iff.mp hw with rfl | rfl <;> simp

omit [Fintype V] [DecidableEq V] in
theorem rank_uV_le {p : ℕ} (x : RefU V p) : sharedRank p (uV p x) ≤ 1 := by
  rcases x with x | x <;> simp [sharedRank]

theorem exists_mem_sym2 {α : Type*} (e : Sym2 α) : ∃ w, w ∈ e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

variable {p : ℕ} {lab : WP (RefU V p) → Fin 2} {X : Finset (Sym2 V)} {hX : ∀ e ∈ X, ¬ e.IsDiag}
  {indices : Finset (RefI V p)}

/-- Root–root library edges are lifted reserve edges. -/
theorem roots_edge (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {e : Sym2 (RefW V p)} (he : e ∈ libU indices (flexB p lab X hX))
    (hall : ∀ x ∈ e, x ∈ sharedRoots p) : ∃ e₀ ∈ X, e = Sym2.map (refEmb p) e₀ := by
  obtain ⟨j, -, -, hcase⟩ := edge_cases_U p lab X hX indices hlib he
  rcases hcase with h | ⟨r, -, hr⟩ | ⟨t, -, ht⟩
  · exact h
  · obtain ⟨v, hv⟩ := mem_sharedRoots.mp (hall _ (midV_mem_of_mem_pathE hr))
    exact absurd hv (midV_not_root v)
  · obtain ⟨w, hw⟩ := exists_mem_sym2 e
    obtain ⟨k, rfl⟩ := tok_vertex_of_mem_tokE ht hw
    obtain ⟨v, hv⟩ := mem_sharedRoots.mp (hall _ hw)
    exact absurd hv (tokV_not_root v)

/-- Adjacent non-root identities have different ranks. -/
theorem rank_ne (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {u v : RefW V p} (hu : u ∉ sharedRoots p)
    (he : s(u, v) ∈ libU indices (flexB p lab X hX)) : sharedRank p u ≠ sharedRank p v := by
  obtain ⟨j, -, -, hcase⟩ := edge_cases_U p lab X hX indices hlib he
  rcases hcase with ⟨e₀, -, h⟩ | ⟨r, -, hr⟩ | ⟨t, -, ht⟩
  · have hu' : u ∈ Sym2.map (refEmb p) e₀ := h ▸ Sym2.mem_mk_left u v
    exact absurd (mem_sharedRoots.mpr (root_of_mem_map_refEmb hu')) hu
  · have hm : sharedRank p (midV p r) = 2 := rfl
    have h1 := rank_uV_le (p := p) (rtS p r).1
    have h2 := rank_uV_le (p := p) (rtS p r).2
    rcases mem_pathE hr with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ <;> omega
  · obtain ⟨k₁, k₂, hk, rfl, rfl⟩ := mem_tokE_pair ht
    intro hrk
    have hk12 : k₁ = k₂ := by
      have e1 : sharedRank p (tokV p t k₁) = 3 + k₁.val := rfl
      have e2 : sharedRank p (tokV p t k₂) = 3 + k₂.val := rfl
      exact Fin.ext (by omega)
    subst hk12
    exact gadget_loopless _ _ hk (Sym2.mk_isDiag_iff.mpr rfl)

/-- Membership in the earlier-neighbour set, unfolded. -/
theorem mem_earlier {u v : RefW V p} :
    u ∈ earlier indices (flexB p lab X hX) (sharedRoots p) (sharedRank p) v ↔
      u ∈ vsupp (libU indices (flexB p lab X hX)) ∧
      s(u, v) ∈ libU indices (flexB p lab X hX) ∧
      (u ∈ sharedRoots p ∨ sharedRank p u < sharedRank p v) := by
  simp only [earlier, nbrs, mem_filter, and_assoc]

/-- The set of possible earlier neighbours of each non-root identity. -/
noncomputable def candEarlier (p : ℕ) : RefW V p → Finset (RefW V p)
  | Sum.inl (Sum.inl _) => ∅
  | Sum.inl (Sum.inr r) => {uV p (rtS p r).1, uV p (rtS p r).2}
  | Sum.inr (t, k) => (univ.filter fun k' : Fin 8 => s(k', k) ∈ gadget t.sign).image (tokV p t)

theorem card_candEarlier_le (w : RefW V p) : (candEarlier p w).card ≤ 2 := by
  rcases w with (x | r) | ⟨t, k⟩
  · simp [candEarlier]
  · exact card_le_two
  · exact card_image_le.trans (card_gadget_nbrs_le _ _)

/-- Every earlier neighbour of a non-root identity is a candidate. -/
theorem earlier_subset_cand
    (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {v : RefW V p} (hv : v ∉ sharedRoots p) :
    earlier indices (flexB p lab X hX) (sharedRoots p) (sharedRank p) v ⊆ candEarlier p v := by
  intro u hu
  obtain ⟨-, hsu, hord⟩ := mem_earlier.mp hu
  obtain ⟨j, -, -, hcase⟩ := edge_cases_U p lab X hX indices hlib hsu
  rcases hcase with ⟨e₀, -, h⟩ | ⟨r, -, hr⟩ | ⟨t, -, ht⟩
  · have hv' : v ∈ Sym2.map (refEmb p) e₀ := h ▸ Sym2.mem_mk_right u v
    exact absurd (mem_sharedRoots.mpr (root_of_mem_map_refEmb hv')) hv
  · rcases mem_pathE hr with ⟨rfl, hx | hx⟩ | ⟨rfl, hx | hx⟩
    · subst hx; simp [candEarlier]
    · subst hx; simp [candEarlier]
    · -- `u` is the middle and `v` an endpoint: the middle is never earlier
      exfalso
      rcases hord with hroot | hlt
      · obtain ⟨w, hw⟩ := mem_sharedRoots.mp hroot
        exact midV_not_root w hw
      · subst hx
        have := rank_uV_le (p := p) (rtS p r).1
        have hm : sharedRank p (midV p r) = 2 := rfl
        omega
    · exfalso
      rcases hord with hroot | hlt
      · obtain ⟨w, hw⟩ := mem_sharedRoots.mp hroot
        exact midV_not_root w hw
      · subst hx
        have := rank_uV_le (p := p) (rtS p r).2
        have hm : sharedRank p (midV p r) = 2 := rfl
        omega
  · obtain ⟨k₁, k₂, hk, rfl, rfl⟩ := mem_tokE_pair ht
    simp only [candEarlier, mem_image, mem_filter, mem_univ, true_and]
    exact ⟨k₁, hk, rfl⟩

theorem earlier_card_le_two
    (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {v : RefW V p} (hv : v ∉ sharedRoots p) :
    (earlier indices (flexB p lab X hX) (sharedRoots p) (sharedRank p) v).card ≤ 2 :=
  (card_le_card (earlier_subset_cand hlib hv)).trans (card_candEarlier_le v)

/-- **Coappearance** of distinct earlier neighbours, checked against the actual pieces. -/
theorem earlier_coappear
    (hlib : ∀ i, (Sum.inl i : RefI V p) ∈ indices → i ∈ (evenRef p X hX).lib)
    {v : RefW V p} (hvU : v ∈ vsupp (libU indices (flexB p lab X hX)))
    (hv : v ∉ sharedRoots p) {u₁ u₂ : RefW V p}
    (h₁ : u₁ ∈ earlier indices (flexB p lab X hX) (sharedRoots p) (sharedRank p) v)
    (h₂ : u₂ ∈ earlier indices (flexB p lab X hX) (sharedRoots p) (sharedRank p) v) :
    Coappear indices (flexB p lab X hX) u₁ u₂ := by
  have hc₁ := earlier_subset_cand hlib hv h₁
  have hc₂ := earlier_subset_cand hlib hv h₂
  obtain ⟨e, he, hve⟩ := mem_vsupp.mp hvU
  obtain ⟨j, hj, hej, hcase⟩ := edge_cases_U p lab X hX indices hlib he
  refine ⟨j, hj, ?_⟩
  rcases hcase with ⟨e₀, -, h⟩ | ⟨r, hrB, hr⟩ | ⟨t, htB, ht⟩
  · exact absurd (mem_sharedRoots.mpr (root_of_mem_map_refEmb (h ▸ hve))) hv
  · -- `v` lies on the path of `r`; it is a non-root, non-hub vertex only as the middle
    have hpath : ∀ w ∈ candEarlier p v, w ∈ vsupp (flexB p lab X hX j) := by
      rcases vertex_of_mem_pathE hr hve with rfl | rfl | rfl
      · intro w hw
        simp only [candEarlier, mem_insert, mem_singleton] at hw
        rcases hw with rfl | rfl
        · exact mem_vsupp.mpr ⟨s(uV p (rtS p r).1, midV p r), hrB (by simp [pathE]),
            Sym2.mem_mk_left _ _⟩
        · exact mem_vsupp.mpr ⟨s(uV p (rtS p r).2, midV p r), hrB (by simp [pathE]),
            Sym2.mem_mk_left _ _⟩
      · intro w hw; simp [candEarlier] at hw
      · intro w hw; simp [candEarlier] at hw
    exact ⟨hpath _ hc₁, hpath _ hc₂⟩
  · obtain ⟨k, rfl⟩ := tok_vertex_of_mem_tokE ht hve
    have htok : ∀ w ∈ candEarlier p (tokV p t k), w ∈ vsupp (flexB p lab X hX j) := by
      intro w hw
      simp only [candEarlier, mem_image, mem_filter, mem_univ, true_and] at hw
      obtain ⟨k', hk', rfl⟩ := hw
      refine mem_vsupp.mpr ⟨s(tokV p t k', tokV p t k), htB ?_, Sym2.mem_mk_left _ _⟩
      exact mem_mapE.mpr ⟨s(k', k), hk', rfl⟩
    exact ⟨htok _ hc₁, htok _ hc₂⟩

end PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared
