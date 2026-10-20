/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrivateTemplate.TriangleBlocks

/-!
# The even-source edge-bijective transformer

Positions are a finite type `I` with a successor permutation `σ`.  The source graph is
`Hx = {x i x (σ i)}` and the target graph is `Hy = {y i y (σ i)}`; injectivity of both edge
maps says that `i ↦ x i x (σ i) ↦ y i y (σ i)` is an edge bijection which is a
homomorphism along closed trails.  (A cycle decomposition of an even graph, followed by
an edge-bijective homomorphism, is exactly such data; target vertices may be identified.)

For fresh vertices `u i = a (i,0)`, `v i = a (i,1)`, `w i = a (i,2)` the transformer `T`
has, for each `i`, the eleven edges
`x_i u_i, x_i v_i, x_i w_i, x_i u_{σi}, y_i u_i, y_i v_i, y_i w_i, y_i u_{σi},
 u_i v_i, w_i u_{σi}, v_i w_i`.
Both `T ∪ Hx` and `T ∪ Hy` have exact triangle decompositions, with triangles
`(x_i, x_{σi}, u_{σi}), (x_i, v_i, w_i), (y_i, u_i, v_i), (y_i, w_i, u_{σi})`
and the same with `x, y` interchanged.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart AntiEdgeSelection

variable {W : Type*} [DecidableEq W] {I : Type*} [Fintype I]

/-- Data of a transformer. -/
structure TransformerData (σ : Equiv.Perm I) (x y : I → W) (a : I × Fin 3 → W) : Prop where
  hx : ∀ i, x i ≠ x (σ i)
  hy : ∀ i, y i ≠ y (σ i)
  hxinj : Function.Injective fun i => s(x i, x (σ i))
  hyinj : Function.Injective fun i => s(y i, y (σ i))
  ha : Function.Injective a
  hax : ∀ p j, a p ≠ x j
  hay : ∀ p j, a p ≠ y j
  hxy : ∀ i j, x i ≠ y j

/-- The eleven transformer edges at position `i`. -/
def transAt (σ : Equiv.Perm I) (x y : I → W) (a : I × Fin 3 → W) (i : I) :
    Finset (Sym2 W) :=
  {s(x i, a (i, 0)), s(x i, a (i, 1)), s(x i, a (i, 2)), s(x i, a (σ i, 0)),
   s(y i, a (i, 0)), s(y i, a (i, 1)), s(y i, a (i, 2)), s(y i, a (σ i, 0)),
   s(a (i, 0), a (i, 1)), s(a (i, 2), a (σ i, 0)), s(a (i, 1), a (i, 2))}

/-- The transformer edge set. -/
def transEdges (σ : Equiv.Perm I) (x y : I → W) (a : I × Fin 3 → W) : Finset (Sym2 W) :=
  univ.biUnion (transAt σ x y a)

/-- The transformer is symmetric in source and target. -/
theorem transEdges_comm (σ : Equiv.Perm I) (x y : I → W) (a : I × Fin 3 → W) :
    transEdges σ x y a = transEdges σ y x a := by
  unfold transEdges
  refine biUnion_congr rfl fun i _ => ?_
  ext e
  simp only [transAt, mem_insert, mem_singleton]
  tauto

omit [DecidableEq W] [Fintype I] in
theorem TransformerData.swap {σ : Equiv.Perm I} {x y : I → W} {a : I × Fin 3 → W}
    (h : TransformerData σ x y a) : TransformerData σ y x a :=
  ⟨h.hy, h.hx, h.hyinj, h.hxinj, h.ha, h.hay, h.hax, fun i j hij => h.hxy j i hij.symm⟩

/-- The four triangle kinds at a position. -/
inductive Kind
  | A
  | B
  | C
  | D
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.A, .B, .C, .D}
  complete := by intro k; cases k <;> simp

/-- First corners of the triangles decomposing `T ∪ Hx`. -/
def triA (x y : I → W) : Kind × I → W
  | (.A, i) => x i
  | (.B, i) => x i
  | (.C, i) => y i
  | (.D, i) => y i

/-- Second corners. -/
def triB (σ : Equiv.Perm I) (x : I → W) (a : I × Fin 3 → W) : Kind × I → W
  | (.A, i) => x (σ i)
  | (.B, i) => a (i, 1)
  | (.C, i) => a (i, 0)
  | (.D, i) => a (i, 2)

/-- Third corners. -/
def triC (σ : Equiv.Perm I) (a : I × Fin 3 → W) : Kind × I → W
  | (.A, i) => a (σ i, 0)
  | (.B, i) => a (i, 2)
  | (.C, i) => a (i, 1)
  | (.D, i) => a (σ i, 0)

variable {σ : Equiv.Perm I} {x y : I → W} {a : I × Fin 3 → W}

set_option hygiene false in
/-- Closing tactic for the transformer case analysis. -/
local macro "tcontra" : tactic => `(tactic| first
  | exact absurd h1 (hax _ _) | exact absurd h1 (hxa _ _) | exact absurd h1 (hay _ _)
  | exact absurd h1 (hya _ _) | exact absurd h1 (hxy _ _) | exact absurd h1 (hyx _ _)
  | exact absurd h1 (hx _) | exact absurd h1 (hy _) | exact absurd h1 (hx' _)
  | exact absurd h1 (hy' _)
  | exact absurd h2 (hax _ _) | exact absurd h2 (hxa _ _) | exact absurd h2 (hay _ _)
  | exact absurd h2 (hya _ _) | exact absurd h2 (hxy _ _) | exact absurd h2 (hyx _ _)
  | exact absurd h2 (hx _) | exact absurd h2 (hy _) | exact absurd h2 (hx' _)
  | exact absurd h2 (hy' _))

set_option hygiene false in
/-- Closing tactic using injectivity of the auxiliaries. -/
local macro "taux" : tactic => `(tactic| first
  | rfl
  | tcontra
  | (obtain ⟨e1, e2⟩ := Prod.mk.inj (h.ha h1)
     first
     | exact absurd e2 (by decide)
     | (subst e1; first | rfl | tcontra)
     | (cases σ.injective e1; first | rfl | tcontra))
  | (obtain ⟨e1, e2⟩ := Prod.mk.inj (h.ha h2)
     first
     | exact absurd e2 (by decide)
     | (subst e1; first | rfl | tcontra)
     | (cases σ.injective e1; first | rfl | tcontra)))

omit [Fintype I] in
theorem TransformerData.goodLabels (h : TransformerData σ x y a) :
    GoodLabels (triA x y) (triB σ x a) (triC σ a) := by
  have hax := h.hax
  have hay := h.hay
  have hxa : ∀ j p, x j ≠ a p := fun j p e => h.hax p j e.symm
  have hya : ∀ j p, y j ≠ a p := fun j p e => h.hay p j e.symm
  have hxy := h.hxy
  have hyx : ∀ i j, y i ≠ x j := fun i j e => h.hxy j i e.symm
  have hx := h.hx
  have hy := h.hy
  have hx' : ∀ i, x (σ i) ≠ x i := fun i e => h.hx i e.symm
  have hy' : ∀ i, y (σ i) ≠ y i := fun i e => h.hy i e.symm
  have haeq : ∀ p q, a p = a q ↔ p = q := fun p q => h.ha.eq_iff
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨k, i⟩; cases k <;> simp [triA, triB, hx, hxa, hya]
  · rintro ⟨k, i⟩; cases k <;> simp [triA, triC, hxa, hya]
  · rintro ⟨k, i⟩; cases k <;> simp [triB, triC, hxa, haeq]
  · rintro ⟨k, i⟩ ⟨k', j⟩ e he he'
    cases k <;> cases k' <;>
      simp only [triA, triB, triC, mem_tri3] at he he' <;>
      rcases he with rfl | rfl | rfl <;> rcases he' with h0 | h0 | h0 <;>
      first
      | (have := h.hxinj h0; subst this; rfl)
      | (rcases Sym2.eq_iff.mp h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> taux)


/-- The source edge set `Hx = {x i x (σ i)}`. -/
abbrev srcEdges (σ : Equiv.Perm I) (x : I → W) : Finset (Sym2 W) :=
  posEdges x fun i => x (σ i)

theorem labelEdges_transformer :
    labelEdges (triA x y) (triB σ x a) (triC σ a) = transEdges σ x y a ∪ srcEdges σ x := by
  ext e
  simp only [mem_labelEdges, mem_union, transEdges, mem_biUnion, mem_univ, true_and,
    mem_posEdges]
  constructor
  · rintro ⟨⟨k, i⟩, he⟩
    cases k <;> simp only [triA, triB, triC, mem_tri3] at he <;>
      rcases he with rfl | rfl | rfl <;>
      solve
      | exact Or.inr ⟨i, rfl⟩
      | (refine Or.inl ⟨i, ?_⟩; simp [transAt])
      | (refine Or.inl ⟨σ i, ?_⟩; simp [transAt])
  · rintro (⟨i, he⟩ | ⟨i, rfl⟩)
    · simp only [transAt, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        solve
        | (refine ⟨(.A, i), ?_⟩; simp [mem_tri3, triA, triB, triC])
        | (refine ⟨(.B, i), ?_⟩; simp [mem_tri3, triA, triB, triC])
        | (refine ⟨(.C, i), ?_⟩; simp [mem_tri3, triA, triB, triC])
        | (refine ⟨(.D, i), ?_⟩; simp [mem_tri3, triA, triB, triC])
        | (refine ⟨(.A, σ.symm i), ?_⟩; simp [mem_tri3, triA, triB, triC])
    · exact ⟨(.A, i), by simp [mem_tri3, triA, triB, triC]⟩

/-- **Transformer, source mode.** `T ∪ Hx` has an exact triangle decomposition. -/
theorem TransformerData.hasDecomp_source (h : TransformerData σ x y a) :
    HasDecomp part1 triFam (transEdges σ x y a ∪ srcEdges σ x) := by
  rw [← labelEdges_transformer]
  exact h.goodLabels.hasDecomp

/-- **Transformer, target mode.** `T ∪ Hy` has an exact triangle decomposition. -/
theorem TransformerData.hasDecomp_target (h : TransformerData σ x y a) :
    HasDecomp part1 triFam (transEdges σ x y a ∪ srcEdges σ y) := by
  rw [transEdges_comm]
  exact h.swap.hasDecomp_source

theorem TransformerData.disjoint_source (h : TransformerData σ x y a) :
    Disjoint (transEdges σ x y a) (srcEdges σ x) := by
  rw [Finset.disjoint_left]
  intro e he he'
  simp only [transEdges, mem_biUnion, mem_univ, true_and] at he
  obtain ⟨i, he⟩ := he
  obtain ⟨j, rfl⟩ := mem_posEdges.mp he'
  have hax := h.hax
  have hxa : ∀ j p, x j ≠ a p := fun j p e => h.hax p j e.symm
  have hxy := h.hxy
  simp only [transAt, mem_insert, mem_singleton, Sym2.eq_iff] at he
  rcases he with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0 <;>
    rcases h0 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    first
    | exact hax _ _ h1.symm | exact hax _ _ h2.symm

theorem TransformerData.disjoint_target (h : TransformerData σ x y a) :
    Disjoint (transEdges σ x y a) (srcEdges σ y) := by
  rw [transEdges_comm]
  exact h.swap.disjoint_source

theorem TransformerData.card_srcEdges (h : TransformerData σ x y a) :
    (srcEdges σ x).card = Fintype.card I :=
  card_posEdges h.hxinj

/-- The transformer has exactly eleven edges per position. -/
theorem TransformerData.card_transEdges (h : TransformerData σ x y a) :
    (transEdges σ x y a).card = 11 * Fintype.card I := by
  have h1 := h.goodLabels.card_labelEdges
  rw [labelEdges_transformer, card_union_of_disjoint h.disjoint_source, h.card_srcEdges,
    Fintype.card_prod] at h1
  have hK : Fintype.card Kind = 4 := by decide
  rw [hK] at h1
  omega


/-- The four transformer spokes at a source vertex. -/
def spoke (σ : Equiv.Perm I) (x : I → W) (a : I × Fin 3 → W) (p : I × Fin 4) : Sym2 W :=
  s(x p.1, ![a (p.1, 0), a (p.1, 1), a (p.1, 2), a (σ p.1, 0)] p.2)

/-- **Root load of the transformer.** A vertex which is neither an auxiliary nor a target
vertex meets exactly four transformer edges per source position at which it sits. -/
theorem TransformerData.incidentLoad_eq (h : TransformerData σ x y a) (z : W)
    (hza : ∀ p, a p ≠ z) (hzy : ∀ i, y i ≠ z) :
    incidentLoad (transEdges σ x y a) z = 4 * (univ.filter fun i => x i = z).card := by
  classical
  have hset : (transEdges σ x y a).filter (fun e => z ∈ e) =
      ((univ.filter fun i => x i = z) ×ˢ (univ : Finset (Fin 4))).image (spoke σ x a) := by
    ext e
    simp only [mem_filter, transEdges, mem_biUnion, mem_univ, true_and, mem_image, mem_product,
      Prod.exists]
    constructor
    · rintro ⟨⟨i, he⟩, hz⟩
      simp only [transAt, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        rcases Sym2.mem_iff.mp hz with hz | hz <;>
        first
        | exact absurd hz.symm (hza _)
        | exact absurd hz.symm (hzy _)
        | (subst hz
           first
           | exact ⟨i, 0, ⟨rfl, trivial⟩, rfl⟩
           | exact ⟨i, 1, ⟨rfl, trivial⟩, rfl⟩
           | exact ⟨i, 2, ⟨rfl, trivial⟩, rfl⟩
           | exact ⟨i, 3, ⟨rfl, trivial⟩, rfl⟩)
    · rintro ⟨i, k, ⟨hi, -⟩, rfl⟩
      refine ⟨⟨i, ?_⟩, ?_⟩
      · fin_cases k <;> simp [spoke, transAt]
      · simp [spoke, hi]
  unfold incidentLoad
  rw [hset, card_image_of_injOn, card_product, card_univ, Fintype.card_fin, mul_comm]
  rintro ⟨i, k⟩ hi ⟨i', k'⟩ hi' he
  simp only [coe_product, Set.mem_prod, mem_coe, mem_filter, mem_univ, true_and, and_true] at hi hi'
  simp only [spoke] at he
  rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, -⟩
  · fin_cases k <;> fin_cases k' <;> dsimp at h2 <;>
      obtain ⟨e1, e2⟩ := Prod.mk.inj (h.ha h2) <;>
      first
      | exact absurd e2 (by decide)
      | (subst e1; rfl)
      | (cases σ.injective e1; rfl)
      | (subst e1; exact absurd (hi'.trans hi.symm) (h.hx _))
      | (subst e1; exact absurd (hi.trans hi'.symm) (h.hx _))
  · fin_cases k' <;> simp at h1 <;> exact absurd h1.symm (h.hax _ _)

end PartitionedTriangleAbsorption.PrivateTemplate
