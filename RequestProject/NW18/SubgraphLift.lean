/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.FracAveraging

/-!
# Auxiliary facts for the proof of Theorem 2.6

* lifting weightings of the triangles of an induced subgraph `G[S]` to `G`;
* degrees after deleting an edge set of small maximum degree, and the stability of
  non-extremality under such deletions;
* counting `k`-sets containing a fixed set.
-/

namespace NashWilliams18

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Lifting weightings from `G[S]` to `G` -/

/-- Lift a weighting of the triangles of `G[S]` (sets of vertices of the subtype) to `G`. -/
noncomputable def liftW (S : Finset V) (w : Finset (S : Set V) → ℝ) : Finset V → ℝ :=
  fun T => if T ⊆ S then w (T.subtype (· ∈ (S : Set V))) else 0

omit [Fintype V] in
lemma liftW_nonneg (S : Finset V) {w : Finset (S : Set V) → ℝ} (hw : ∀ t, 0 ≤ w t) (T : Finset V) :
    0 ≤ liftW S w T := by
  unfold liftW; split_ifs
  · exact hw _
  · exact le_rfl

omit [Fintype V] in
lemma liftW_of_not_subset (S : Finset V) (w : Finset (S : Set V) → ℝ) {T : Finset V}
    (hT : ¬ T ⊆ S) : liftW S w T = 0 := by
  simp [liftW, hT]

omit [Fintype V] in
lemma map_subtype_eq (S : Finset V) (T : Finset V) (hT : T ⊆ S) :
    (T.subtype (· ∈ (S : Set V))).map (Function.Embedding.subtype _) = T :=
  subtype_map_of_mem (fun x hx => by simpa using hT hx)

omit [Fintype V] in
lemma subtype_map_eq (S : Finset V) (T' : Finset (S : Set V)) :
    (T'.map (Function.Embedding.subtype _)).subtype (· ∈ (S : Set V)) = T' := by
  ext x
  exact mem_subtype.trans (mem_map' (Function.Embedding.subtype _))

omit [Fintype V] [DecidableEq V] in
lemma isNClique_induce_iff (G : SimpleGraph V) (S : Finset V) (T' : Finset (S : Set V)) :
    (G.induce (S : Set V)).IsNClique 3 T' ↔
      G.IsNClique 3 (T'.map (Function.Embedding.subtype _)) := by
  constructor
  · rintro ⟨hc, hcard⟩
    refine ⟨fun x hx y hy hxy => ?_, by rw [card_map]; exact hcard⟩
    simp only [coe_map, Set.mem_image, mem_coe, Function.Embedding.coe_subtype] at hx hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    exact hc hx' hy' (fun h => hxy (by rw [h]))
  · rintro ⟨hc, hcard⟩
    refine ⟨fun x hx y hy hxy => ?_, by rw [card_map] at hcard; exact hcard⟩
    have := hc (mem_map_of_mem (Function.Embedding.subtype _) hx)
      (mem_map_of_mem (Function.Embedding.subtype _) hy)
      (fun h => hxy (Subtype.ext h))
    exact this

/-- Loads of a lifted weighting at an edge inside `S`. -/
lemma load_liftW (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (w : Finset (S : Set V) → ℝ) {u v : V} (hu : u ∈ S) (hv : v ∈ S) :
    load G (liftW S w) u v = load (G.induce (S : Set V)) w ⟨u, by simpa using hu⟩
      ⟨v, by simpa using hv⟩ := by
  unfold load
  rw [← sum_filter_of_ne (p := fun T => T ⊆ S) (fun T _ hT => by
    by_contra h; exact hT (liftW_of_not_subset S w h))]
  symm
  refine sum_bij' (fun T' _ => T'.map (Function.Embedding.subtype _))
    (fun T _ => T.subtype (· ∈ (S : Set V))) ?_ ?_ ?_ ?_ ?_
  · intro T' hT'
    simp only [mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hT' ⊢
    refine ⟨⟨(isNClique_induce_iff G S T').mp hT'.1, ?_, ?_⟩, ?_⟩
    · exact mem_map_of_mem _ hT'.2.1
    · exact mem_map_of_mem _ hT'.2.2
    · intro x hx
      simp only [mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, _, rfl⟩ := hx
      simp
  · intro T hT
    simp only [mem_filter, SimpleGraph.mem_cliqueFinset_iff] at hT ⊢
    obtain ⟨⟨hc, hu', hv'⟩, hTS⟩ := hT
    refine ⟨?_, by simpa using hu', by simpa using hv'⟩
    rw [isNClique_induce_iff, map_subtype_eq S T hTS]
    exact hc
  · intro T' _
    exact subtype_map_eq S T'
  · intro T hT
    simp only [mem_filter] at hT
    exact map_subtype_eq S T hT.2
  · intro T' _
    have hsub : T'.map (Function.Embedding.subtype _) ⊆ S := by
      intro x hx
      simp only [mem_map, Function.Embedding.coe_subtype] at hx
      obtain ⟨y, _, rfl⟩ := hx
      simp
    simp only [liftW, if_pos hsub, subtype_map_eq]

/-- Loads of a lifted weighting at an edge not inside `S` vanish. -/
lemma load_liftW_of_not_mem (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (w : Finset (S : Set V) → ℝ) {u v : V} (h : ¬ (u ∈ S ∧ v ∈ S)) :
    load G (liftW S w) u v = 0 := by
  unfold load
  refine sum_eq_zero fun T hT => liftW_of_not_subset S w fun hTS => h ?_
  simp only [mem_filter] at hT
  exact ⟨hTS hT.2.1, hTS hT.2.2⟩

/-! ### Deleting an edge set of small maximum degree -/

omit [Fintype V] in
lemma degree_deleteEdges_ge [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset (Sym2 V)) (v : V) :
    G.degree v ≤ (del G H).degree v + (H.filter (fun f => v ∈ f)).card := by
  rw [← G.card_neighborFinset_eq_degree, ← (del G H).card_neighborFinset_eq_degree]
  have hsub : G.neighborFinset v ⊆ (del G H).neighborFinset v ∪
      (univ.filter (fun w => s(v, w) ∈ H)) := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    by_cases hH : s(v, w) ∈ H
    · exact mem_union_right _ (by simp [hH])
    · exact mem_union_left _ (by simp [del, SimpleGraph.deleteEdges_adj, hw, hH])
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  gcongr
  apply card_le_card_of_injOn (fun w => s(v, w))
  · intro w hw
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hw
    simp only [coe_filter, Set.mem_setOf_eq]
    exact ⟨hw, Sym2.mem_mk_left _ _⟩
  · intro w₁ _ w₂ _ h
    rcases (by simpa using h : w₁ = w₂ ∨ v = w₂ ∧ w₁ = v) with h | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1

lemma degree_deleteEdges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset (Sym2 V)) (v : V) : (del G H).degree v ≤ G.degree v := by
  rw [← G.card_neighborFinset_eq_degree, ← (del G H).card_neighborFinset_eq_degree]
  apply card_le_card
  intro w hw
  simp only [SimpleGraph.mem_neighborFinset, del, SimpleGraph.deleteEdges_adj] at hw ⊢
  exact hw.1

lemma minDegree_deleteEdges_ge (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset (Sym2 V)) (d : ℕ) (hH : ∀ v, (H.filter (fun f => v ∈ f)).card ≤ d) :
    G.minDegree ≤ (del G H).minDegree + d := by
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [SimpleGraph.minDegree, Finset.univ_eq_empty]
  obtain ⟨v, hv⟩ := (del G H).exists_minimal_degree_vertex
  rw [hv]
  calc G.minDegree ≤ G.degree v := G.minDegree_le_degree v
    _ ≤ (del G H).degree v + (H.filter (fun f => v ∈ f)).card := degree_deleteEdges_ge G H v
    _ ≤ (del G H).degree v + d := by gcongr; exact hH v

lemma cutSize_deleteEdges_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (H : Finset (Sym2 V)) (S : Finset V) : cutSize (del G H) S ≤ cutSize G S := by
  unfold cutSize
  apply card_le_card
  intro e he
  simp only [mem_filter, SimpleGraph.mem_edgeFinset] at he ⊢
  refine ⟨?_, he.2⟩
  exact (SimpleGraph.edgeSet_mono (SimpleGraph.deleteEdges_le _)) he.1

/-- Non-extremality survives the deletion of an edge set of maximum degree `≤ σ n / 4`. -/
lemma not_extremal_deleteEdges (G : SimpleGraph V) [DecidableRel G.Adj] {σ : ℝ} (hσ : 0 ≤ σ)
    (H : Finset (Sym2 V)) (d : ℕ) (hH : ∀ v, (H.filter (fun f => v ∈ f)).card ≤ d)
    (hd : (d : ℝ) ≤ σ * Fintype.card V / 4) (hG : ¬ IsExtremal (σ / 2) G) :
    ¬ IsExtremal (σ / 4) (del G H) := by
  rintro ⟨h1, S, h2⟩
  apply hG
  refine ⟨?_, S, ?_⟩
  · refine le_trans ?_ (le_trans h1 ?_)
    · exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    · exact_mod_cast card_le_card (monotone_filter_right _ fun v _ hv => by
        have h := degree_deleteEdges_ge G H v
        have h' : (G.degree v : ℝ) ≤ (del G H).degree v + d := by
          exact_mod_cast h.trans (by gcongr; exact hH v)
        linarith)
  · have := cutSize_deleteEdges_le G H S
    have h3 : (cutSize (del G H) S : ℝ) ≤ cutSize G S := by exact_mod_cast this
    have : 0 ≤ (Fintype.card V : ℝ) ^ 2 := sq_nonneg _
    nlinarith

/-! ### Counting `k`-sets through a fixed set -/

/-- At most `C(n - a, k - a)` sets of size `k` contain a fixed set of size `a`. -/
lemma card_supsets_le (A : Finset V) (k : ℕ) :
    ((univ.powersetCard k).filter (fun S => A ⊆ S)).card ≤
      (Fintype.card V - A.card).choose (k - A.card) := by
  have : ((univ.powersetCard k).filter (fun S => A ⊆ S)).card ≤
      ((univ \ A).powersetCard (k - A.card)).card := by
    apply card_le_card_of_injOn (fun S => S \ A)
    · intro S hS
      simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq] at hS
      rw [mem_coe, mem_powersetCard]
      refine ⟨sdiff_subset_sdiff (subset_univ _) (subset_refl A), ?_⟩
      rw [card_sdiff_of_subset hS.2, hS.1]
    · intro S hS S' hS' h
      simp only [coe_filter, mem_powersetCard, subset_univ, true_and, Set.mem_setOf_eq]
        at hS hS'
      have h1 := sdiff_union_of_subset hS.2
      have h2 := sdiff_union_of_subset hS'.2
      simp only at h
      rw [← h1, ← h2, h]
  refine this.trans (le_of_eq ?_)
  rw [card_powersetCard, card_sdiff_of_subset (subset_univ _), card_univ]

end NashWilliams18
