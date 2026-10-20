/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Assembly
public import PartitionedTriangleAbsorption.SignedHinge.Gadget
public import PartitionedTriangleAbsorption.SignedHinge.Wedge
public import PartitionedTriangleAbsorption.SignedHinge.Expansion

/-! # Occurrence data, slots, wedges and local blocks

`OccData` records, for every occurrence `o`, the roots `a b c` of its certificate triangle,
the apex `x` of the fresh copy `{a,b,x}`, the hinge `H` for `{a,b,c}, {a,b,x}`, and the two
further apices `y, z` supplied by `hinge_gadget`. Slot `(o,k)` has base edge
`ab, ac, bc` (`k = 0, 1, 2`), apex `x, y, z`, slot triangle `{base, apex}` and slot wedge
(the two apex edges). `OccGood` collects the facts proved by the selection and the gadget.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ} {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {O : Type*}

/-- Chosen data of all occurrence gadgets. -/
structure OccData (V O : Type*) where
  a : O → V
  b : O → V
  c : O → V
  x : O → V
  y : O → V
  z : O → V
  H : O → Finset (Sym2 V)

namespace OccData

variable (D : OccData V O)

/-- The non-root support of the occurrence hinge. -/
def fresh (o : O) : Finset V := vertSet (D.H o) \ {D.a o, D.b o, D.c o}

/-- First base vertex of a slot. -/
def bu (σ : O × Fin 3) : V := ![D.a σ.1, D.a σ.1, D.b σ.1] σ.2

/-- Second base vertex of a slot. -/
def bv (σ : O × Fin 3) : V := ![D.b σ.1, D.c σ.1, D.c σ.1] σ.2

/-- Apex of a slot. -/
def ap (σ : O × Fin 3) : V := ![D.x σ.1, D.y σ.1, D.z σ.1] σ.2

/-- Slot wedge: the two edges from the apex to the base. -/
def wedge (σ : O × Fin 3) : Finset (Sym2 V) := {s(D.bu σ, D.ap σ), s(D.bv σ, D.ap σ)}

/-- Slot triangle. -/
def tri (σ : O × Fin 3) : Finset V := {D.bu σ, D.bv σ, D.ap σ}

/-- The local closure `Y o`: the occurrence hinge minus the four `y,z` wedge edges. -/
def core (o : O) : Finset (Sym2 V) :=
  D.H o \ {s(D.a o, D.y o), s(D.c o, D.y o), s(D.b o, D.z o), s(D.c o, D.z o)}

end OccData

/-- Facts about one chosen occurrence gadget. -/
structure OccGood (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (Z' : Finset V) (D : OccData V O) (o : O) : Prop where
  hab : D.a o ≠ D.b o
  hac : D.a o ≠ D.c o
  hbc : D.b o ≠ D.c o
  copy : IsCopy p F G {D.a o, D.b o, D.c o}
  roots : ({D.a o, D.b o, D.c o} : Finset V) ⊆ Z'
  adj_ax : G.Adj (D.a o) (D.x o)
  adj_xb : G.Adj (D.x o) (D.b o)
  part_x : p (D.x o) = p (D.c o)
  sub : ∀ e ∈ D.H o, e ∈ G.edgeSet
  hinge : IsHinge p F {D.a o, D.b o, D.c o} {D.a o, D.b o, D.x o} (D.H o)
  x_fresh : D.x o ∈ D.fresh o
  fresh_disj : Disjoint (D.fresh o) Z'
  ya : D.y o ≠ D.a o
  yb : D.y o ≠ D.b o
  yc : D.y o ≠ D.c o
  yx : D.y o ≠ D.x o
  za : D.z o ≠ D.a o
  zb : D.z o ≠ D.b o
  zc : D.z o ≠ D.c o
  zx : D.z o ≠ D.x o
  yz : D.y o ≠ D.z o
  triY : IsTypedTri p F {D.a o, D.c o, D.y o}
  triZ : IsTypedTri p F {D.b o, D.c o, D.z o}
  ay : s(D.a o, D.y o) ∈ D.H o
  cy : s(D.c o, D.y o) ∈ D.H o
  bz : s(D.b o, D.z o) ∈ D.H o
  cz : s(D.c o, D.z o) ∈ D.H o
  dec_core : HasDecomp p F (D.core o)
  dec_block : HasDecomp p F (D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)})

namespace OccGood

variable {G : SimpleGraph V} {Z' : Finset V} {D : OccData V O} {o : O}

theorem adj_of_mem (h : OccGood p F G Z' D o) {u v : V} (huv : s(u, v) ∈ D.H o) :
    G.Adj u v :=
  h.sub _ huv

theorem y_fresh (h : OccGood p F G Z' D o) : D.y o ∈ D.fresh o :=
  mem_sdiff.mpr ⟨mem_vertSet_of_mem h.ay (Sym2.mem_mk_right _ _), by
    simp [h.ya, h.yb, h.yc]⟩

theorem z_fresh (h : OccGood p F G Z' D o) : D.z o ∈ D.fresh o :=
  mem_sdiff.mpr ⟨mem_vertSet_of_mem h.bz (Sym2.mem_mk_right _ _), by
    simp [h.za, h.zb, h.zc]⟩

theorem x_ne_a (h : OccGood p F G Z' D o) : D.x o ≠ D.a o := fun he =>
  (mem_sdiff.mp h.x_fresh).2 (by simp [he])

theorem x_ne_b (h : OccGood p F G Z' D o) : D.x o ≠ D.b o := fun he =>
  (mem_sdiff.mp h.x_fresh).2 (by simp [he])

theorem x_ne_c (h : OccGood p F G Z' D o) : D.x o ≠ D.c o := fun he =>
  (mem_sdiff.mp h.x_fresh).2 (by simp [he])

theorem not_mem_Z' (h : OccGood p F G Z' D o) {v : V} (hv : v ∈ D.fresh o) : v ∉ Z' :=
  disjoint_left.mp h.fresh_disj hv

end OccGood

namespace OccData

variable {G : SimpleGraph V} {Z' : Finset V} (D : OccData V O)

theorem ap_fresh (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) : D.ap σ ∈ D.fresh σ.1 := by
  obtain ⟨o, k⟩ := σ
  fin_cases k
  · exact (h o).x_fresh
  · exact (h o).y_fresh
  · exact (h o).z_fresh

omit [Fintype V] in
theorem bu_mem (σ : O × Fin 3) : D.bu σ ∈ ({D.a σ.1, D.b σ.1, D.c σ.1} : Finset V) := by
  obtain ⟨o, k⟩ := σ
  fin_cases k <;> simp [bu]

omit [Fintype V] in
theorem bv_mem (σ : O × Fin 3) : D.bv σ ∈ ({D.a σ.1, D.b σ.1, D.c σ.1} : Finset V) := by
  obtain ⟨o, k⟩ := σ
  fin_cases k <;> simp [bv]

theorem bu_ne_bv (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) : D.bu σ ≠ D.bv σ := by
  obtain ⟨o, k⟩ := σ
  fin_cases k
  · exact (h o).hab
  · exact (h o).hac
  · exact (h o).hbc

omit [Fintype V] [DecidableEq V] in
theorem base_eq (σ : O × Fin 3) :
    s(D.bu σ, D.bv σ) = edgeOf (D.a σ.1) (D.b σ.1) (D.c σ.1) σ.2 := by
  obtain ⟨o, k⟩ := σ
  fin_cases k <;> rfl

theorem bu_Z' (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) : D.bu σ ∈ Z' :=
  (h σ.1).roots (D.bu_mem σ)

theorem bv_Z' (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) : D.bv σ ∈ Z' :=
  (h σ.1).roots (D.bv_mem σ)

theorem ap_not_Z' (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) : D.ap σ ∉ Z' :=
  (h σ.1).not_mem_Z' (D.ap_fresh h σ)

theorem bu_ne_ap (h : ∀ o, OccGood p F G Z' D o) (σ τ : O × Fin 3) : D.bu σ ≠ D.ap τ :=
  fun he => D.ap_not_Z' h τ (he ▸ D.bu_Z' h σ)

theorem bv_ne_ap (h : ∀ o, OccGood p F G Z' D o) (σ τ : O × Fin 3) : D.bv σ ≠ D.ap τ :=
  fun he => D.ap_not_Z' h τ (he ▸ D.bv_Z' h σ)

/-- Apices are pairwise distinct. -/
theorem ap_inj (h : ∀ o, OccGood p F G Z' D o)
    (hF : ∀ o o', o ≠ o' → Disjoint (D.fresh o) (D.fresh o')) {σ τ : O × Fin 3}
    (he : D.ap σ = D.ap τ) : σ = τ := by
  by_cases ho : σ.1 = τ.1
  · obtain ⟨o, k⟩ := σ
    obtain ⟨o', k'⟩ := τ
    simp only at ho
    subst ho
    have := h o
    fin_cases k <;> fin_cases k' <;> simp only [ap, Fin.zero_eta, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Fin.reduceFinMk] at he ⊢
    all_goals first
      | rfl
      | exact absurd he this.yx
      | exact absurd he.symm this.yx
      | exact absurd he this.zx
      | exact absurd he.symm this.zx
      | exact absurd he this.yz
      | exact absurd he.symm this.yz
  · exact absurd (by rw [he]; exact D.ap_fresh h τ)
      (disjoint_left.mp (hF _ _ ho) (D.ap_fresh h σ))

/-- Slot triangles are `F`-copies. -/
theorem tri_copy (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) :
    IsCopy p F G (D.tri σ) := by
  obtain ⟨o, k⟩ := σ
  have ho := h o
  obtain ⟨hAab, hAac, hAbc⟩ := SimpleGraph.is3Clique_triple_iff.mp ho.copy.1
  fin_cases k
  · change IsCopy p F G {D.a o, D.b o, D.x o}
    refine isCopy_three hAab ho.adj_ax ho.adj_xb.symm ?_
    rw [map_three p ho.hab (Ne.symm ho.x_ne_a) (Ne.symm ho.x_ne_b), ho.part_x,
      ← map_three p ho.hab ho.hac ho.hbc]
    exact ho.copy.2
  · change IsCopy p F G {D.a o, D.c o, D.y o}
    exact isCopy_three hAac (ho.adj_of_mem ho.ay) (ho.adj_of_mem ho.cy) ho.triY.2
  · change IsCopy p F G {D.b o, D.c o, D.z o}
    exact isCopy_three hAbc (ho.adj_of_mem ho.bz) (ho.adj_of_mem ho.cz) ho.triZ.2

end OccData

end PartitionedTriangleAbsorption.SignedHinge

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ} {p : V → Fin t}
  {F : Finset (Multiset (Fin t))} {O : Type*}
  {G : SimpleGraph V} {Z' : Finset V}

namespace OccData

variable (D : OccData V O)

omit [Fintype V] in
theorem wedges_of_occ [Fintype O] [DecidableEq O] (o : O) :
    (univ.filter fun σ : O × Fin 3 => σ.1 = o).biUnion D.wedge =
      {s(D.a o, D.x o), s(D.b o, D.x o), s(D.a o, D.y o), s(D.c o, D.y o),
        s(D.b o, D.z o), s(D.c o, D.z o)} := by
  ext e
  simp only [mem_biUnion, mem_filter, mem_univ, true_and, Prod.exists]
  constructor
  · rintro ⟨o', k, rfl, he⟩
    fin_cases k <;> simp only [wedge, bu, bv, ap, mem_insert, mem_singleton] at he ⊢ <;>
      tauto
  · intro he
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨o, 0, rfl, by simp [wedge, bu, ap]⟩
    · exact ⟨o, 0, rfl, by simp [wedge, bv, ap]⟩
    · exact ⟨o, 1, rfl, by simp [wedge, bu, ap]⟩
    · exact ⟨o, 1, rfl, by simp [wedge, bv, ap]⟩
    · exact ⟨o, 2, rfl, by simp [wedge, bu, ap]⟩
    · exact ⟨o, 2, rfl, by simp [wedge, bv, ap]⟩

theorem block_eq [Fintype O] [DecidableEq O] (h : ∀ o, OccGood p F G Z' D o) (o : O) :
    localBlock Prod.fst D.core D.wedge o = D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)} := by
  have ho := h o
  rw [localBlock, wedges_of_occ]
  ext e
  simp only [core, mem_union, mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro (⟨he, -⟩ | he | he | he | he | he | he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
    all_goals subst he
    · exact Or.inl ho.ay
    · exact Or.inl ho.cy
    · exact Or.inl ho.bz
    · exact Or.inl ho.cz
  · rintro (he | he | he)
    · by_cases h4 : e = s(D.a o, D.y o) ∨ e = s(D.c o, D.y o) ∨ e = s(D.b o, D.z o) ∨
          e = s(D.c o, D.z o)
      · right; right; right; tauto
      · exact Or.inl ⟨he, h4⟩
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (Or.inl he))

theorem block_vertSet (h : ∀ o, OccGood p F G Z' D o) (o : O) :
    vertSet (D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)}) ⊆
      {D.a o, D.b o, D.c o} ∪ D.fresh o := by
  intro v hv
  rw [vertSet_union, mem_union] at hv
  rcases hv with hv | hv
  · by_cases hr : v ∈ ({D.a o, D.b o, D.c o} : Finset V)
    · exact mem_union_left _ hr
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hv, hr⟩)
  · obtain ⟨e, he, hve⟩ := mem_vertSet.mp hv
    simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl <;> rcases Sym2.mem_iff.mp hve with rfl | rfl
    · simp
    · exact mem_union_right _ (h o).x_fresh
    · simp
    · exact mem_union_right _ (h o).x_fresh

theorem block_no_inside (h : ∀ o, OccGood p F G Z' D o) (o : O) :
    ∀ e ∈ D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)}, (∀ v ∈ e, v ∈ Z') → False := by
  intro e he hZ
  have ho := h o
  rcases mem_union.mp he with he | he
  · have hroot : ∀ v ∈ e, v ∈ ({D.a o, D.b o, D.c o} : Finset V) := by
      intro v hv
      by_contra hr
      exact ho.not_mem_Z' (mem_sdiff.mpr ⟨mem_vertSet_of_mem he hv, hr⟩) (hZ v hv)
    have htri := mem_triEdges_of_endpoints (ho.sub e he) hroot
    exact disjoint_left.mp ho.hinge.1 he (mem_union_left _ htri)
  · simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact ho.not_mem_Z' ho.x_fresh (hZ _ (Sym2.mem_mk_right _ _))
    · exact ho.not_mem_Z' ho.x_fresh (hZ _ (Sym2.mem_mk_right _ _))

theorem block_sub (h : ∀ o, OccGood p F G Z' D o) (o : O) :
    ∀ e ∈ D.H o ∪ {s(D.a o, D.x o), s(D.b o, D.x o)}, e ∈ G.edgeSet := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact (h o).sub e he
  · simp only [mem_insert, mem_singleton] at he
    rcases he with rfl | rfl
    · exact (h o).adj_ax
    · exact (h o).adj_xb.symm

omit [Fintype V] in
theorem core_subset (o : O) : D.core o ⊆ D.H o := sdiff_subset

theorem core_wedge_disj (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) :
    Disjoint (D.core σ.1) (D.wedge σ) := by
  obtain ⟨o, k⟩ := σ
  have ho := h o
  rw [disjoint_left]
  intro e he hw
  fin_cases k
  · have hx : e ∈ triEdges ({D.a o, D.b o, D.x o} : Finset V) := by
      rw [triEdges_three ho.hab (Ne.symm ho.x_ne_a) (Ne.symm ho.x_ne_b)]
      simp only [wedge, bu, bv, ap, mem_insert, mem_singleton] at hw
      simp only [mem_insert, mem_singleton]
      simp at hw
      tauto
    exact disjoint_left.mp ho.hinge.1 (D.core_subset o he) (mem_union_right _ hx)
  all_goals
    simp only [wedge, bu, bv, ap, mem_insert, mem_singleton] at hw
    simp only [core, mem_sdiff, mem_insert, mem_singleton] at he
    simp at hw
    tauto

theorem wedge_vertSet (σ : O × Fin 3) :
    vertSet (D.wedge σ) ⊆ {D.bu σ, D.bv σ, D.ap σ} := by
  intro v hv
  obtain ⟨e, he, hve⟩ := mem_vertSet.mp hv
  simp only [wedge, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl <;> rcases Sym2.mem_iff.mp hve with rfl | rfl <;> simp

theorem wedge_disj (h : ∀ o, OccGood p F G Z' D o)
    (hF : ∀ o o', o ≠ o' → Disjoint (D.fresh o) (D.fresh o')) {σ σ' : O × Fin 3}
    (hne : σ ≠ σ') : Disjoint (D.wedge σ) (D.wedge σ') := by
  have key : ∀ u u' : V, u ∈ Z' → u' ∈ Z' → s(u, D.ap σ) ≠ s(u', D.ap σ') := by
    intro u u' hu hu' he
    rcases Sym2.eq_iff.mp he with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact hne (D.ap_inj h hF h2)
    · exact D.ap_not_Z' h σ' (h1 ▸ hu)
  rw [disjoint_left]
  intro e he he'
  simp only [wedge, mem_insert, mem_singleton] at he he'
  rcases he with rfl | rfl <;> rcases he' with he' | he'
  · exact key _ _ (D.bu_Z' h σ) (D.bu_Z' h σ') he'
  · exact key _ _ (D.bu_Z' h σ) (D.bv_Z' h σ') he'
  · exact key _ _ (D.bv_Z' h σ) (D.bu_Z' h σ') he'
  · exact key _ _ (D.bv_Z' h σ) (D.bv_Z' h σ') he'

theorem wedge_sub (h : ∀ o, OccGood p F G Z' D o) (σ : O × Fin 3) :
    ∀ e ∈ D.wedge σ, e ∈ G.edgeSet := by
  obtain ⟨-, h2, h3⟩ := SimpleGraph.is3Clique_triple_iff.mp (D.tri_copy h σ).1
  intro e he
  simp only [wedge, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl
  · exact h2
  · exact h3

end OccData

end PartitionedTriangleAbsorption.SignedHinge
