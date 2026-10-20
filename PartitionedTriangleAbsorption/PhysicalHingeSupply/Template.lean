/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Gadget
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

/-! # The seven-edge, six-vertex physical hinge template and its transport

Template vertices (`Fin 6`): `0 = u, 1 = v, 2 = w, 3 = z, 4 = x, 5 = y`.
Root copies `S = {u,v,w}`, `S' = {u,v,z}` share exactly the edge `uv`.
The hinge is `H = {uy, vx, xw, yw, xz, yz, xy}` with exact modes

* `uyw, vxw, xyz` decomposing `H ∪ {uw, vw}`;
* `uyz, vxz, xyw` decomposing `H ∪ {uz, vz}`.

Typing (`templateHinge`): if the label of `x` equals that of `u` and the label of `y`
equals that of `v`, every mode triangle has the label multiset of one root copy, so the
template is an `F`-hinge for **every** type family `F` containing the two root types
(in particular for `F0`, and whether or not the two root types differ).

Transport (`isHinge_map`): hinges, decompositions and edge sets move along any vertex
embedding `Fin 6 ↪ V`; `hingeEdges_isHinge` is the resulting statement for six distinct
physical vertices, phrased with the explicit physical edge set `hingeEdges`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PhysicalHingeSupply

open Finset SignedHinge

/-! ### The finite template -/

/-- First root copy `{u, v, w}`. -/
def rootS : Finset (Fin 6) := {0, 1, 2}
/-- Second root copy `{u, v, z}`. -/
def rootS' : Finset (Fin 6) := {0, 1, 3}
/-- Template hinge `{uy, vx, xw, yw, xz, yz, xy}`. -/
def tmplH : Finset (Sym2 (Fin 6)) :=
  {s(0, 5), s(1, 4), s(4, 2), s(5, 2), s(4, 3), s(5, 3), s(4, 5)}
/-- First mode `uyw, vxw, xyz`. -/
def modeD : Finset (Finset (Fin 6)) := {{0, 5, 2}, {1, 4, 2}, {4, 5, 3}}
/-- Second mode `uyz, vxz, xyw`. -/
def modeD' : Finset (Finset (Fin 6)) := {{0, 5, 3}, {1, 4, 3}, {4, 5, 2}}

theorem tmplH_card : tmplH.card = 7 := by decide

theorem tmpl_disjoint : Disjoint tmplH (triEdges rootS ∪ triEdges rootS') := by
  unfold tmplH triEdges rootS rootS'
  decide

theorem tmpl_first_edges : modeD.biUnion triEdges = tmplH ∪ (triEdges rootS \ triEdges rootS') := by
  unfold modeD tmplH triEdges rootS rootS'
  decide

theorem tmpl_second_edges :
    modeD'.biUnion triEdges = tmplH ∪ (triEdges rootS' \ triEdges rootS) := by
  unfold modeD' tmplH triEdges rootS rootS'
  decide

theorem tmpl_first_disjoint : (modeD : Set (Finset (Fin 6))).PairwiseDisjoint triEdges := by
  intro a ha b hb hab
  simp only [modeD, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)

theorem tmpl_second_disjoint : (modeD' : Set (Finset (Fin 6))).PairwiseDisjoint triEdges := by
  intro a ha b hb hab
  simp only [modeD', coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | exact absurd rfl hab | (unfold Function.onFun triEdges; decide)

section Typing

variable {t : ℕ} {F : Finset (Multiset (Fin t))}

/-- Label multiset of a three-element template triangle. -/
theorem tri_val_map (ℓ : Fin 6 → Fin t) {a b c : Fin 6}
    (h : ({a, b, c} : Finset (Fin 6)).val = a ::ₘ b ::ₘ {c}) :
    ({a, b, c} : Finset (Fin 6)).val.map ℓ = ℓ a ::ₘ ℓ b ::ₘ {ℓ c} := by
  rw [h]; simp

/-- **Typing of both exact modes.** Every mode triangle has the label multiset of a root
copy, as soon as `x` carries the label of `u` and `y` the label of `v`. -/
theorem tmpl_typed (ℓ : Fin 6 → Fin t) (h4 : ℓ 4 = ℓ 0) (h5 : ℓ 5 = ℓ 1)
    (hS : rootS.val.map ℓ ∈ F) (hS' : rootS'.val.map ℓ ∈ F) :
    (∀ s ∈ modeD, IsTypedTri ℓ F s) ∧ ∀ s ∈ modeD', IsTypedTri ℓ F s := by
  have eS : rootS.val.map ℓ = ℓ 0 ::ₘ ℓ 1 ::ₘ {ℓ 2} := tri_val_map ℓ (by decide)
  have eS' : rootS'.val.map ℓ = ℓ 0 ::ₘ ℓ 1 ::ₘ {ℓ 3} := tri_val_map ℓ (by decide)
  rw [eS] at hS
  rw [eS'] at hS'
  refine ⟨?_, ?_⟩
  · intro s hs
    simp only [modeD, mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map ℓ (by decide), h5]; exact hS
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map ℓ (by decide), h4, Multiset.cons_swap]; exact hS
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map ℓ (by decide), h4, h5]; exact hS'
  · intro s hs
    simp only [modeD', mem_insert, mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map ℓ (by decide), h5]; exact hS'
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map ℓ (by decide), h4, Multiset.cons_swap]; exact hS'
    · refine ⟨by decide, ?_⟩
      rw [tri_val_map ℓ (by decide), h4, h5]; exact hS

/-- **The template is an `F`-hinge** for the two root copies, for every labelling with
`ℓ x = ℓ u`, `ℓ y = ℓ v` whose root copies are typed. -/
theorem templateHinge (ℓ : Fin 6 → Fin t) (h4 : ℓ 4 = ℓ 0) (h5 : ℓ 5 = ℓ 1)
    (hS : rootS.val.map ℓ ∈ F) (hS' : rootS'.val.map ℓ ∈ F) :
    IsHinge ℓ F rootS rootS' tmplH := by
  have h := tmpl_typed ℓ h4 h5 hS hS'
  exact ⟨tmpl_disjoint, ⟨modeD, h.1, tmpl_first_disjoint, tmpl_first_edges⟩,
    ⟨modeD', h.2, tmpl_second_disjoint, tmpl_second_edges⟩⟩

end Typing

/-! ### Transport along a vertex embedding (generic in the type family) -/

section Transport

variable {W V : Type*} [DecidableEq W] [DecidableEq V] {t : ℕ} {F : Finset (Multiset (Fin t))}

/-- Edge embedding induced by a vertex embedding. -/
def edgeEmb (f : W ↪ V) : Sym2 W ↪ Sym2 V := ⟨Sym2.map f, Sym2.map.injective f.injective⟩

/-- Vertex-set embedding induced by a vertex embedding. -/
def setEmb (f : W ↪ V) : Finset W ↪ Finset V := ⟨fun s => s.map f, map_injective f⟩

theorem triEdges_map (f : W ↪ V) (s : Finset W) :
    triEdges (s.map f) = (triEdges s).map (edgeEmb f) := by
  simp only [map_eq_image, triEdges, sym2_image, filter_image, Sym2.isDiag_map f.injective]
  rfl

theorem isDecomp_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} {D : Finset (Finset W)}
    (h : IsDecomp pW F E D) : IsDecomp pV F (E.map (edgeEmb f)) (D.map (setEmb f)) := by
  obtain ⟨hT, hP, hU⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨s', hs', rfl⟩ := mem_map.mp hs
    refine ⟨by simpa [setEmb] using (hT s' hs').1, ?_⟩
    simp only [setEmb, Function.Embedding.coeFn_mk, map_val, Multiset.map_map]
    have : pV ∘ f = pW := funext hp
    rw [this]; exact (hT s' hs').2
  · intro s hs u hu hsu
    simp only [coe_map, Set.mem_image, mem_coe] at hs hu
    obtain ⟨s', hs', rfl⟩ := hs
    obtain ⟨u', hu', rfl⟩ := hu
    have hne : s' ≠ u' := fun h => hsu (by rw [h])
    simp only [Function.onFun, setEmb, Function.Embedding.coeFn_mk, triEdges_map]
    exact (disjoint_map _).mpr (hP hs' hu' hne)
  · rw [← hU]
    ext e
    simp only [mem_biUnion, mem_map, setEmb, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨s, ⟨s', hs', rfl⟩, he⟩
      rw [triEdges_map] at he
      obtain ⟨e', he', rfl⟩ := mem_map.mp he
      exact ⟨e', ⟨s', hs', he'⟩, rfl⟩
    · rintro ⟨e', ⟨s', hs', he'⟩, rfl⟩
      refine ⟨s'.map f, ⟨s', hs', rfl⟩, ?_⟩
      rw [triEdges_map]
      exact mem_map_of_mem _ he'

theorem hasDecomp_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) {E : Finset (Sym2 W)} (h : HasDecomp pW F E) :
    HasDecomp pV F (E.map (edgeEmb f)) := by
  obtain ⟨D, hD⟩ := h
  exact ⟨_, isDecomp_map f hp hD⟩

/-- **Hinges transport along vertex embeddings.** -/
theorem isHinge_map (f : W ↪ V) {pW : W → Fin t} {pV : V → Fin t}
    (hp : ∀ w, pV (f w) = pW w) {S S' : Finset W} {H : Finset (Sym2 W)}
    (h : IsHinge pW F S S' H) :
    IsHinge pV F (S.map f) (S'.map f) (H.map (edgeEmb f)) := by
  obtain ⟨hd, h1, h2⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [triEdges_map, triEdges_map, ← map_union]
    exact (disjoint_map _).mpr hd
  · rw [triEdges_map, triEdges_map, ← map_sdiff, ← map_union]
    exact hasDecomp_map f hp h1
  · rw [triEdges_map, triEdges_map, ← map_sdiff, ← map_union]
    exact hasDecomp_map f hp h2

end Transport

/-! ### The physical hinge on six distinct vertices -/

section Physical

variable {V : Type*} [DecidableEq V] {t : ℕ} {F : Finset (Multiset (Fin t))}

/-- The physical seven-edge set `{uy, vx, xw, yw, xz, yz, xy}`. -/
def hingeEdges (u v w z x y : V) : Finset (Sym2 V) :=
  {s(u, y), s(v, x), s(x, w), s(y, w), s(x, z), s(y, z), s(x, y)}

/-- Six pairwise distinct vertices `u, v, w, z, x, y`. -/
def SixDistinct (u v w z x y : V) : Prop :=
  u ≠ v ∧ u ≠ w ∧ u ≠ z ∧ u ≠ x ∧ u ≠ y ∧ v ≠ w ∧ v ≠ z ∧ v ≠ x ∧ v ≠ y ∧
    w ≠ z ∧ w ≠ x ∧ w ≠ y ∧ z ≠ x ∧ z ≠ y ∧ x ≠ y

/-- The labelling map `Fin 6 → V`, `(0,…,5) ↦ (u,v,w,z,x,y)`. -/
def sixMap (u v w z x y : V) : Fin 6 → V := ![u, v, w, z, x, y]

omit [DecidableEq V] in
theorem sixMap_injective {u v w z x y : V} (h : SixDistinct u v w z x y) :
    Function.Injective (sixMap u v w z x y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [sixMap, eq_comm]

/-- The vertex embedding of the template. -/
def sixEmb {u v w z x y : V} (h : SixDistinct u v w z x y) : Fin 6 ↪ V :=
  ⟨sixMap u v w z x y, sixMap_injective h⟩

theorem rootS_map {u v w z x y : V} (h : SixDistinct u v w z x y) :
    rootS.map (sixEmb h) = {u, v, w} := by
  simp [rootS, sixEmb, sixMap]

theorem rootS'_map {u v w z x y : V} (h : SixDistinct u v w z x y) :
    rootS'.map (sixEmb h) = {u, v, z} := by
  simp [rootS', sixEmb, sixMap]

theorem tmplH_map {u v w z x y : V} (h : SixDistinct u v w z x y) :
    tmplH.map (edgeEmb (sixEmb h)) = hingeEdges u v w z x y := by
  simp [tmplH, hingeEdges, edgeEmb, sixEmb, sixMap]

/-- **The physical hinge.** For six distinct vertices with `p x = p u`, `p y = p v` and
typed root copies `{u,v,w}`, `{u,v,z}`, the explicit edge set `hingeEdges u v w z x y`
is an `F`-hinge for the two copies. -/
theorem hingeEdges_isHinge {p : V → Fin t} {u v w z x y : V} (h : SixDistinct u v w z x y)
    (hx : p x = p u) (hy : p y = p v)
    (hS : ({u, v, w} : Finset V).val.map p ∈ F) (hS' : ({u, v, z} : Finset V).val.map p ∈ F) :
    IsHinge p F {u, v, w} {u, v, z} (hingeEdges u v w z x y) := by
  set f := sixEmb h
  have hfS : (rootS.map f).val.map p = rootS.val.map (p ∘ f) := by
    simp only [map_val, Multiset.map_map]
  have hfS' : (rootS'.map f).val.map p = rootS'.val.map (p ∘ f) := by
    simp only [map_val, Multiset.map_map]
  have hT := templateHinge (F := F) (p ∘ f) (by simpa [f, sixEmb, sixMap] using hx)
    (by simpa [f, sixEmb, sixMap] using hy)
    (by rw [← hfS, rootS_map h]; exact hS) (by rw [← hfS', rootS'_map h]; exact hS')
  have hM := isHinge_map f (pV := p) (fun _ => rfl) hT
  rwa [rootS_map h, rootS'_map h, tmplH_map h] at hM

end Physical

end PartitionedTriangleAbsorption.PhysicalHingeSupply
