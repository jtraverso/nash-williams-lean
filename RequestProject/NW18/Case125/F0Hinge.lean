/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Defs
public import RequestProject.NW18.HingeCount
public import RequestProject.NW18.WalkCount

@[expose] public section

/-!
# Explicit `F₀`-hinges (towards Claim 14.6.4)

For two `F₀`-copies `T₁ = u₁u₂v₁`, `T₂ = u₁u₂v₂` of a two-partitioned graph the proof of
Claim 14.6.4 uses three kinds of hinges:

* the eight-vertex hinges of type 1 and type 2 of `HingeModel.lean` (bipyramids over a
  6-cycle), with all new vertices in prescribed parts, when `u₁, u₂` lie in the same part;
* a six-vertex hinge (`mH6`: two new vertices `x, y`, with `x ~ u₁, v₁, v₂, y` and
  `y ~ u₂, v₁, v₂`) when `u₁, u₂` lie in different parts.

All are verified once on a model vertex set (by `decide`) and transported along the injective
map given by the vertices; the transport lemmas of `HingeModel.lean` are extended here to
partitioned graphs.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)

lemma mem_F0_iff (i j k : Fin 2) :
    ({i, j, k} : Multiset (Fin 2)) ∈ F0 ↔ ¬ (i = j ∧ j = k) := by
  revert i j k; decide

lemma triple_val_map {V : Type*} [DecidableEq V] {t : ℕ} (p : V → Fin t) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z)
    (hyz : y ≠ z) : ({x, y, z} : Finset V).val.map p = {p x, p y, p z} := by
  have h1 : x ∉ ({y, z} : Finset V) := by simp [hxy, hxz]
  have h2 : y ∉ ({z} : Finset V) := by simp [hyz]
  rw [Finset.insert_val_of_notMem h1, Finset.insert_val_of_notMem h2]
  simp

/-! ### Transport of partitioned decompositions and hinges -/

section Transport

variable {W V : Type*} [DecidableEq W] [DecidableEq V] {t : ℕ}

lemma isDecomp_map_typed (f : W ↪ V) {q : W → Fin t} {p : V → Fin t}
    (hpq : ∀ w, p (f w) = q w) {F : Finset (Multiset (Fin t))} {E : Finset (Sym2 W)}
    {D : Finset (Finset W)} (h : IsDecomp q F E D) :
    IsDecomp p F (E.map f.sym2Map) (D.map (finsetMapEmb f)) := by
  obtain ⟨hT, hdisj, hU⟩ := h
  refine ⟨fun s hs => ?_, fun s hs t ht hst => ?_, ?_⟩
  · simp only [mem_map, finsetMapEmb, Function.Embedding.coeFn_mk] at hs
    obtain ⟨s, hs, rfl⟩ := hs
    refine ⟨by rw [card_map]; exact (hT s hs).1, ?_⟩
    have : (s.map f).val.map p = s.val.map q := by
      rw [Finset.map_val, Multiset.map_map]; congr 1; funext w; exact hpq w
    rw [this]; exact (hT s hs).2
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

lemma isHinge_map_typed (f : W ↪ V) {q : W → Fin t} {p : V → Fin t}
    (hpq : ∀ w, p (f w) = q w) {F : Finset (Multiset (Fin t))} {S S' : Finset W}
    {H : Finset (Sym2 W)} (h : IsHinge q F S S' H) :
    IsHinge p F (S.map f) (S'.map f) (H.map f.sym2Map) := by
  obtain ⟨hd, ⟨D₁, hD₁⟩, ⟨D₂, hD₂⟩⟩ := h
  refine ⟨?_, ⟨D₁.map (finsetMapEmb f), ?_⟩, ⟨D₂.map (finsetMapEmb f), ?_⟩⟩
  · rw [triEdges_map, triEdges_map, ← map_union, disjoint_map]; exact hd
  · rw [triEdges_map, triEdges_map, ← Finset.map_sdiff, ← map_union]
    exact isDecomp_map_typed f hpq hD₁
  · rw [triEdges_map, triEdges_map, ← Finset.map_sdiff, ← map_union]
    exact isDecomp_map_typed f hpq hD₂

lemma isDecomp_of_typed (q : W → Fin t) (F : Finset (Multiset (Fin t))) (E : Finset (Sym2 W))
    (D : Finset (Finset W)) (h1 : ∀ s ∈ D, IsTypedTri q F s)
    (h2 : ∀ s ∈ D, ∀ t ∈ D, s ≠ t → Disjoint (triEdges s) (triEdges t))
    (h3 : D.biUnion triEdges = E) : IsDecomp q F E D :=
  ⟨h1, fun s hs t ht hst => h2 s hs t ht hst, h3⟩

end Transport

/-! ### The typed eight-vertex models -/

/-- Parts for the type-1 hinge: `u₁, u₂, x₁, …, x₄` in part `a`, `v₁, v₂` in part `b`. -/
def q1 (a b : Fin 2) : Fin 8 → Fin 2 := ![a, a, b, b, a, a, a, a]

/-- Parts for the type-2 hinge: `u₁, u₂, w` in part `a`, `v₁, v₂` and the path `a b c` in
part `b`. -/
def q2 (a b : Fin 2) : Fin 8 → Fin 2 := ![a, a, b, b, a, b, b, b]

lemma model_hinge1_F0 (a b : Fin 2) (hab : a ≠ b) : IsHinge (q1 a b) F0 mT1 mT2 mH1 := by
  refine ⟨by decide +kernel, ⟨{{2, 0, 4}, {3, 4, 5}, {2, 5, 6}, {3, 6, 7}, {2, 7, 1}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩,
    ⟨{{3, 0, 4}, {2, 4, 5}, {3, 5, 6}, {2, 6, 7}, {3, 7, 1}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩⟩ <;>
  · unfold IsTypedTri
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | decide +kernel

lemma model_hinge2_F0 (a b : Fin 2) (hab : a ≠ b) : IsHinge (q2 a b) F0 mT1 mT2 mH2 := by
  refine ⟨by decide +kernel, ⟨{{4, 0, 2}, {1, 2, 5}, {4, 5, 6}, {1, 6, 7}, {4, 7, 3}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩,
    ⟨{{4, 2, 5}, {1, 5, 6}, {4, 6, 7}, {1, 7, 3}, {4, 3, 0}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩⟩ <;>
  · unfold IsTypedTri
    fin_cases a <;> fin_cases b <;> first | exact absurd rfl hab | decide +kernel

/-! ### The six-vertex model
Vertices: `0 = u₁, 1 = u₂, 2 = v₁, 3 = v₂, 4 = x, 5 = y`. -/

/-- Model of `T₁ = u₁u₂v₁`. -/
def mS1 : Finset (Fin 6) := {0, 1, 2}
/-- Model of `T₂ = u₁u₂v₂`. -/
def mS2 : Finset (Fin 6) := {0, 1, 3}
/-- The six-vertex hinge. -/
def mH6 : Finset (Sym2 (Fin 6)) :=
  {s(0, 4), s(1, 5), s(2, 4), s(2, 5), s(3, 4), s(3, 5), s(4, 5)}

/-- Parts of the six model vertices. -/
def q6 (a₁ a₂ b₁ b₂ c d : Fin 2) : Fin 6 → Fin 2 := ![a₁, a₂, b₁, b₂, c, d]

lemma model_hinge6_F0 (a₁ a₂ b₁ b₂ c d : Fin 2)
    (h1 : ¬ (b₁ = a₁ ∧ a₁ = c)) (h2 : ¬ (b₁ = a₂ ∧ a₂ = d)) (h3 : ¬ (b₂ = c ∧ c = d))
    (h4 : ¬ (b₂ = a₁ ∧ a₁ = c)) (h5 : ¬ (b₂ = a₂ ∧ a₂ = d)) (h6 : ¬ (b₁ = c ∧ c = d)) :
    IsHinge (q6 a₁ a₂ b₁ b₂ c d) F0 mS1 mS2 mH6 := by
  refine ⟨by decide +kernel, ⟨{{2, 0, 4}, {2, 1, 5}, {3, 4, 5}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩,
    ⟨{{3, 0, 4}, {3, 1, 5}, {2, 4, 5}},
    isDecomp_of_typed _ _ _ _ ?_ (by decide +kernel) (by decide +kernel)⟩⟩ <;>
  · unfold IsTypedTri
    revert h1 h2 h3 h4 h5 h6
    revert a₁ a₂ b₁ b₂ c d
    decide +kernel

lemma vertSet_mH6 : vertSet mH6 = univ := by decide +kernel

end NashWilliams18
