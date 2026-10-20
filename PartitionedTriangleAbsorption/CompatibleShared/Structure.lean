/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CompatibleShared.Producer
public import PartitionedTriangleAbsorption.CompatibleShared.GreedyMain

/-! # The actual compressed F0 library: edge classification, order and coappearance

Vertex classes of `RefW V p = W1 (WP (RefU V p)) (LibIdx (RefU V p))`:
original roots `refEmb p v`, hubs `uV (Sum.inr i)`, request middles `midV r` and token
vertices `tokV t k`. For every library index whose parity part lies in the even library,
every edge of the concrete piece `flexB p lab X hX j` is

* a lifted reserve edge `Sym2.map (refEmb p) e₀` with `e₀ ∈ X` (root–root), or
* one of the two edges of the request path `pathE p r` (realised by `ParityRealize.physA`),
  and then the **whole** path lies in the piece, or
* an edge of a token gadget `tokE t`, and then the **whole** gadget lies in the piece.

Robust-matching metadata never creates an edge between two tokens. From this we verify
the rank order (roots, hubs, request middles, token vertices by gadget index) with at most
two earlier neighbours, pairwise coappearing.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared

open Finset AntiEdgeSelection TypedRefinerCharge TypedApplicationLinks UniversalRefiner
open SharedGreedyPort

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A vertex of `RefU V p` (original or hub) inside `RefW V p`. -/
abbrev uV (p : ℕ) (x : RefU V p) : RefW V p := Sum.inl (Sum.inl x)

/-- The labelled middle vertex of a request. -/
abbrev midV (p : ℕ) (r : Req (RefU V p)) : RefW V p := Sum.inl (Sum.inr r)

/-- Vertex `k` of token `t`. -/
abbrev tokV (p : ℕ) (t : Tok (LibIdx (RefU V p))) (k : Fin 8) : RefW V p := Sum.inr (t, k)

/-- Request roots used by the compressed refiner. -/
noncomputable abbrev rtS (p : ℕ) : Req (RefU V p) → RefU V p × RefU V p :=
  rtP (heapH p) (hubOf p 0)

/-- The two-edge path realising request `r`. -/
noncomputable def pathE (p : ℕ) (r : Req (RefU V p)) : Finset (Sym2 (RefW V p)) :=
  {s(uV p (rtS p r).1, midV p r), s(uV p (rtS p r).2, midV p r)}

/-- The rank: roots `0`, hubs `1`, request middles `2`, token vertex `k` gets `3 + k`. -/
def sharedRank (p : ℕ) : RefW V p → ℕ
  | Sum.inl (Sum.inl (Sum.inl _)) => 0
  | Sum.inl (Sum.inl (Sum.inr _)) => 1
  | Sum.inl (Sum.inr _) => 2
  | Sum.inr (_, k) => 3 + k.val

/-- The roots of the library: all original vertices. -/
def sharedRoots (p : ℕ) : Finset (RefW V p) := univ.image (refEmb p)

theorem pathE_eq (p : ℕ) (r : Req (RefU V p)) :
    liftE (κ := LibIdx (RefU V p)) (physA (rtS p) (Sum.inl r)) = pathE p r := by
  simp [liftE, mapE, physA, pathE, image_insert, image_singleton]

omit [Fintype V] [DecidableEq V] in
theorem refEmb_injective (p : ℕ) : Function.Injective (refEmb (V := V) p) := by
  intro a b h
  simpa [refEmb] using h

theorem mem_sharedRoots {p : ℕ} {w : RefW V p} : w ∈ sharedRoots p ↔ ∃ v, refEmb p v = w := by
  simp [sharedRoots]

/-- **Edge classification** of the concrete F0 pieces. -/
theorem edge_cases (p : ℕ) (lab : WP (RefU V p) → Fin 2) (X : Finset (Sym2 V))
    (hX : ∀ e ∈ X, ¬ e.IsDiag)
    {j : RefI V p} (hj : ∀ i, j = Sum.inl i → i ∈ (evenRef p X hX).lib)
    {e : Sym2 (RefW V p)} (he : e ∈ flexB p lab X hX j) :
    (∃ e₀ ∈ X, e = Sym2.map (refEmb p) e₀) ∨
      (∃ r, pathE p r ⊆ flexB p lab X hX j ∧ e ∈ pathE p r) ∨
      (∃ t, tokE t ⊆ flexB p lab X hX j ∧ e ∈ tokE t) := by
  have hB : flexB p lab X hX j = liftE ((evenRef p X hX).oldPart j) ∪
      tokU ((evenRef p X hX).ids lab j) := rfl
  rw [hB] at he ⊢
  rcases mem_union.mp he with hl | ht
  · obtain ⟨e₁, he₁, rfl⟩ := mem_mapE.mp hl
    rcases j with i | j
    · have hi : i ∈ evenLib (mapE Sum.inl X) (heapH p) (p + 1) (hubOf p 0) := hj i rfl
      have hP : (evenRef p X hX).oldPart (Sum.inl i) =
          physE (rtS p) (UniversalRefiner.piece (mapE Sum.inl X) (heapH p) i) := rfl
      rw [hP] at he₁ ⊢
      obtain ⟨a, ha, he₁a⟩ := mem_biUnion.mp he₁
      have hA := piece_subset (mapE Sum.inl X) (heapH p) (p + 1) 0
        (evenLib_subset (hubOf p 0) hi) ha
      rcases a with r | e₂
      · right; left
        refine ⟨r, ?_, ?_⟩
        · rw [← pathE_eq]
          intro e' he'
          obtain ⟨e'', he'', rfl⟩ := mem_mapE.mp he'
          exact mem_union_left _ (mem_mapE.mpr ⟨e'', mem_biUnion.mpr ⟨_, ha, he''⟩, rfl⟩)
        · rw [← pathE_eq]
          exact mem_mapE.mpr ⟨e₁, he₁a, rfl⟩
      · left
        have hX' : e₂ ∈ mapE Sum.inl X := by
          rcases mem_union.mp hA with h | h
          · rcases mem_union.mp h with h | h
            · obtain ⟨l, -, hl⟩ := mem_biUnion.mp h
              exact absurd hl inr_not_mem_levelAtoms
            · simp [adjRem] at h
          · obtain ⟨e₃, he₃, h3⟩ := mem_image.mp h
            exact (Sum.inr_injective h3) ▸ he₃
        obtain ⟨e₀, he₀, rfl⟩ := mem_mapE.mp hX'
        have h1 : e₁ = Sym2.map Sum.inl (Sym2.map Sum.inl e₀) := by
          simpa [physA] using he₁a
        subst h1
        refine ⟨e₀, he₀, ?_⟩
        induction e₀ using Sym2.ind with
        | _ a b => rfl
    · simp [EvenRefiner.oldPart] at he₁
  · obtain ⟨t, htS, het⟩ := mem_biUnion.mp ht
    right; right
    exact ⟨t, fun e' he' => mem_union_right _ (mem_biUnion.mpr ⟨t, htS, he'⟩), het⟩

theorem mem_pathE {p : ℕ} {r : Req (RefU V p)} {u v : RefW V p}
    (h : s(u, v) ∈ pathE p r) :
    (v = midV p r ∧ (u = uV p (rtS p r).1 ∨ u = uV p (rtS p r).2)) ∨
      (u = midV p r ∧ (v = uV p (rtS p r).1 ∨ v = uV p (rtS p r).2)) := by
  simp only [pathE, mem_insert, mem_singleton, Sym2.eq_iff] at h
  rcases h with (⟨h1, h2⟩ | ⟨h1, h2⟩) | (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact Or.inl ⟨h2, Or.inl h1⟩
  · exact Or.inr ⟨h1, Or.inl h2⟩
  · exact Or.inl ⟨h2, Or.inr h1⟩
  · exact Or.inr ⟨h1, Or.inr h2⟩

theorem midV_mem_of_mem_pathE {p : ℕ} {r : Req (RefU V p)} {e : Sym2 (RefW V p)}
    (h : e ∈ pathE p r) : midV p r ∈ e := by
  simp only [pathE, mem_insert, mem_singleton] at h
  rcases h with rfl | rfl <;> exact Sym2.mem_mk_right _ _

omit [Fintype V] in
theorem mem_tokE_pair {p : ℕ} {t : Tok (LibIdx (RefU V p))} {u v : RefW V p}
    (h : s(u, v) ∈ tokE (W0 := WP (RefU V p)) t) :
    ∃ k₁ k₂, s(k₁, k₂) ∈ gadget t.sign ∧ u = tokV p t k₁ ∧ v = tokV p t k₂ := by
  obtain ⟨e', he', hee⟩ := mem_mapE.mp h
  induction e' using Sym2.ind with
  | _ a b =>
    simp only [map_pair, Sym2.eq_iff] at hee
    rcases hee with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨a, b, he', h1.symm, h2.symm⟩
    · exact ⟨b, a, by rw [Sym2.eq_swap]; exact he', h2.symm, h1.symm⟩

omit [Fintype V] in
theorem tok_vertex_of_mem_tokE {p : ℕ} {t : Tok (LibIdx (RefU V p))} {e : Sym2 (RefW V p)}
    (h : e ∈ tokE (W0 := WP (RefU V p)) t) {w : RefW V p} (hw : w ∈ e) :
    ∃ k, w = tokV p t k :=
  mem_tokE_vertex h hw

omit [Fintype V] [DecidableEq V] in
theorem root_of_mem_map_refEmb {p : ℕ} {e₀ : Sym2 V} {w : RefW V p}
    (hw : w ∈ Sym2.map (refEmb p) e₀) : ∃ v, refEmb p v = w := by
  obtain ⟨v, -, rfl⟩ := Sym2.mem_map.mp hw
  exact ⟨v, rfl⟩

/-- Gadget vertices have at most two gadget neighbours. -/
theorem card_gadget_nbrs_le (b : Bool) (k : Fin 8) :
    (univ.filter fun k' : Fin 8 => s(k', k) ∈ gadget b).card ≤ 2 := by
  refine le_trans ?_ (gadget_incidentLoad_le b k)
  unfold incidentLoad
  refine card_le_card_of_injOn (fun k' => s(k', k)) ?_ ?_
  · intro k' hk'
    exact mem_filter.mpr ⟨(mem_filter.mp hk').2, Sym2.mem_mk_right _ _⟩
  · intro a _ c _ h
    exact Sym2.congr_left.mp h

end PartitionedTriangleAbsorption.TypedRefinerF0.CompressedHub.CompatibleShared
