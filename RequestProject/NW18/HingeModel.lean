/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Defs

@[expose] public section

/-!
# Explicit `K₃`-hinges on eight vertices (towards Lemma 14.4)

For two triangles `T₁ = u₁u₂v₁` and `T₂ = u₁u₂v₂` sharing the edge `u₁u₂`, the paper's hinges
in Lemma 14.4 are *bipyramids over a 6-cycle* with `T₁ ∪ T₂` removed:

* type 1: poles `v₁, v₂` over the cycle `u₁ x₁ x₂ x₃ x₄ u₂` (a path of length 5 from `u₁` to
  `u₂` in the common neighbourhood of `v₁, v₂`);
* type 2: poles `u₂, w` over the cycle `u₁ v₁ a b c v₂` (`w` a common neighbour of
  `u₁, v₁, v₂`, and `v₁ a b c v₂` a path in the common neighbourhood of `w, u₂`).

Both are verified once on the vertex set `Fin 8` (by `decide`) and transported into the host
graph along the injective map given by the eight vertices.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

/-! ### The models on `Fin 8`
Vertices: `0 = u₁, 1 = u₂, 2 = v₁, 3 = v₂`, and `4, 5, 6, 7` are `x₁, …, x₄` (type 1) or
`w, a, b, c` (type 2). -/

/-- Model of `T₁ = u₁u₂v₁`. -/
def mT1 : Finset (Fin 8) := {0, 1, 2}
/-- Model of `T₂ = u₁u₂v₂`. -/
def mT2 : Finset (Fin 8) := {0, 1, 3}

/-- Model hinge of type 1. -/
def mH1 : Finset (Sym2 (Fin 8)) :=
  {s(2, 4), s(2, 5), s(2, 6), s(2, 7), s(3, 4), s(3, 5), s(3, 6), s(3, 7),
    s(0, 4), s(4, 5), s(5, 6), s(6, 7), s(7, 1)}

/-- Model hinge of type 2. -/
def mH2 : Finset (Sym2 (Fin 8)) :=
  {s(1, 5), s(1, 6), s(1, 7), s(4, 0), s(4, 2), s(4, 5), s(4, 6), s(4, 7), s(4, 3),
    s(2, 5), s(5, 6), s(6, 7), s(7, 3)}

lemma isDecomp_onePart_of {W : Type*} [Fintype W] [DecidableEq W] (E : Finset (Sym2 W))
    (D : Finset (Finset W)) (h1 : ∀ s ∈ D, s.card = 3)
    (h2 : ∀ s ∈ D, ∀ t ∈ D, s ≠ t → Disjoint (triEdges s) (triEdges t))
    (h3 : D.biUnion triEdges = E) : IsDecomp onePart K3fam E D :=
  ⟨fun s hs => ⟨h1 s hs, by rw [map_onePart (h1 s hs)]; simp [K3fam]⟩,
    fun s hs t ht hst => h2 s hs t ht hst, h3⟩

lemma model_hinge1 : IsHinge onePart K3fam mT1 mT2 mH1 := by
  refine ⟨by decide +kernel, ⟨{{2, 0, 4}, {3, 4, 5}, {2, 5, 6}, {3, 6, 7}, {2, 7, 1}},
    isDecomp_onePart_of _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩,
    ⟨{{3, 0, 4}, {2, 4, 5}, {3, 5, 6}, {2, 6, 7}, {3, 7, 1}},
    isDecomp_onePart_of _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩⟩

lemma model_hinge2 : IsHinge onePart K3fam mT1 mT2 mH2 := by
  refine ⟨by decide +kernel, ⟨{{4, 0, 2}, {1, 2, 5}, {4, 5, 6}, {1, 6, 7}, {4, 7, 3}},
    isDecomp_onePart_of _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩,
    ⟨{{4, 2, 5}, {1, 5, 6}, {4, 6, 7}, {1, 7, 3}, {4, 3, 0}},
    isDecomp_onePart_of _ _ (by decide +kernel) (by decide +kernel) (by decide +kernel)⟩⟩

lemma vertSet_mH1 : vertSet mH1 = univ := by decide +kernel
lemma vertSet_mH2 : vertSet mH2 = univ := by decide +kernel

/-! ### Transport along an injective map -/

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]

omit [Fintype W] [Fintype V] in
lemma triEdges_map (f : W ↪ V) (s : Finset W) :
    triEdges (s.map f) = (triEdges s).map f.sym2Map := by
  ext e
  induction e using Sym2.ind with
  | _ x y =>
    rw [mk_mem_triEdges]
    constructor
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨b, hb, rfl⟩ := Finset.mem_map.mp hy
      exact Finset.mem_map.mpr
        ⟨s(a, b), mk_mem_triEdges.mpr ⟨ha, hb, fun h => hxy (by rw [h])⟩, rfl⟩
    · intro h
      obtain ⟨e, he, hee⟩ := Finset.mem_map.mp h
      induction e using Sym2.ind with
      | _ a b =>
        obtain ⟨ha, hb, hab⟩ := mk_mem_triEdges.mp he
        simp only [Function.Embedding.sym2Map_apply, Sym2.map_mk, Sym2.eq_iff] at hee
        rcases hee with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨mem_map_of_mem f ha, mem_map_of_mem f hb, fun h => hab (f.injective h)⟩
        · exact ⟨mem_map_of_mem f hb, mem_map_of_mem f ha, fun h => hab (f.injective h).symm⟩

/-- The embedding `s ↦ f '' s` on finite sets. -/
def finsetMapEmb (f : W ↪ V) : Finset W ↪ Finset V := ⟨fun s => s.map f, map_injective f⟩

omit [Fintype W] [Fintype V] in
lemma isDecomp_map (f : W ↪ V) {E : Finset (Sym2 W)} {D : Finset (Finset W)}
    (h : IsDecomp onePart K3fam E D) :
    IsDecomp onePart K3fam (E.map f.sym2Map) (D.map (finsetMapEmb f)) := by
  obtain ⟨hT, hdisj, hU⟩ := h
  refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_, ?_⟩
  · simp only [mem_map, finsetMapEmb, Function.Embedding.coeFn_mk] at hs
    obtain ⟨s, hs, rfl⟩ := hs
    have h3 : (s.map f).card = 3 := by rw [card_map]; exact (hT s hs).1
    exact ⟨h3, by rw [map_onePart h3]; simp [K3fam]⟩
  · simp only [coe_map, Set.mem_image, mem_coe, finsetMapEmb, Function.Embedding.coeFn_mk]
      at hs ht
    obtain ⟨s, hs, rfl⟩ := hs
    obtain ⟨t, ht, rfl⟩ := ht
    have hst' : s ≠ t := fun h => hst (by rw [h])
    show Disjoint (triEdges (s.map f)) (triEdges (t.map f))
    rw [triEdges_map, triEdges_map, disjoint_map]
    exact hdisj hs ht hst'
  · rw [← hU]
    ext e
    simp only [mem_biUnion, mem_map, finsetMapEmb, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, he⟩
      rw [triEdges_map, mem_map] at he
      obtain ⟨e', he', rfl⟩ := he
      exact ⟨e', ⟨s, hs, he'⟩, rfl⟩
    · rintro ⟨e', ⟨s, hs, he'⟩, rfl⟩
      exact ⟨s.map f, ⟨s, hs, rfl⟩, by rw [triEdges_map]; exact mem_map_of_mem _ he'⟩

omit [Fintype W] [Fintype V] in
lemma isHinge_map (f : W ↪ V) {S S' : Finset W} {H : Finset (Sym2 W)}
    (h : IsHinge onePart K3fam S S' H) :
    IsHinge onePart K3fam (S.map f) (S'.map f) (H.map f.sym2Map) := by
  obtain ⟨hd, ⟨D₁, hD₁⟩, ⟨D₂, hD₂⟩⟩ := h
  refine ⟨?_, ⟨D₁.map (finsetMapEmb f), ?_⟩, ⟨D₂.map (finsetMapEmb f), ?_⟩⟩
  · rw [triEdges_map, triEdges_map, ← map_union, disjoint_map]; exact hd
  · rw [triEdges_map, triEdges_map, ← Finset.map_sdiff, ← map_union]; exact isDecomp_map f hD₁
  · rw [triEdges_map, triEdges_map, ← Finset.map_sdiff, ← map_union]; exact isDecomp_map f hD₂

omit [Fintype W] in
lemma vertSet_map (f : W ↪ V) (H : Finset (Sym2 W)) [Fintype W] :
    vertSet (H.map f.sym2Map) = (vertSet H).map f := by
  ext v
  simp only [vertSet, mem_filter, mem_univ, true_and, mem_map, Function.Embedding.sym2Map_apply]
  constructor
  · rintro ⟨_, ⟨e, he, rfl⟩, hv⟩
    rw [Sym2.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨w, ⟨e, he, hw⟩, rfl⟩
  · rintro ⟨w, ⟨e, he, hw⟩, rfl⟩
    exact ⟨_, ⟨e, he, rfl⟩, Sym2.mem_map.mpr ⟨w, hw, rfl⟩⟩

end NashWilliams18
