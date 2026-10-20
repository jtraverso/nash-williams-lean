/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.OnePartDivisibility
public import PartitionedTriangleAbsorption.ReturnedDivisibility
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic.DeriveFintype

/-!
# Labelled triangle blocks

Generic bookkeeping for exact ordinary triangle decompositions given by an explicit,
finitely indexed list of triangles.  If the triangles of distinct labels never share an
edge, their vertex sets form an `IsDecomp part1 triFam` of the union of their edges, and the
union has exactly three edges per label.

The subdivision block `H ∪ ∇H` (each edge `ab` of `H` together with a fresh path `a c b`)
is the first instance.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateTemplate

open Finset OnePart

variable {W : Type*} [DecidableEq W]

/-- The three edges of the triangle on `a, b, c`. -/
def tri3 (a b c : W) : Finset (Sym2 W) := {s(a, b), s(a, c), s(b, c)}

theorem mem_tri3 {a b c : W} {e : Sym2 W} :
    e ∈ tri3 a b c ↔ e = s(a, b) ∨ e = s(a, c) ∨ e = s(b, c) := by
  simp [tri3]

theorem card_tri3 {a b c : W} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (tri3 a b c).card = 3 := by
  rw [tri3, card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simp [hab, hac]
  · simp [hab, hac, hbc]

theorem card_three {a b c : W} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a, b, c} : Finset W).card = 3 := by
  rw [card_insert_of_notMem, card_insert_of_notMem, card_singleton]
  · simpa using hbc
  · simp [hab, hac]

section Labels

variable {L : Type*} [Fintype L]

/-- The edge set covered by a labelled triangle family. -/
def labelEdges (ta tb tc : L → W) : Finset (Sym2 W) :=
  univ.biUnion fun l => tri3 (ta l) (tb l) (tc l)

/-- The vertex sets of a labelled triangle family. -/
def labelTris (ta tb tc : L → W) : Finset (Finset W) :=
  univ.image fun l => ({ta l, tb l, tc l} : Finset W)

variable (ta tb tc : L → W)

/-- Hypotheses on a labelled triangle family: three distinct corners, and triangles with
different labels share no edge. -/
structure GoodLabels : Prop where
  hab : ∀ l, ta l ≠ tb l
  hac : ∀ l, ta l ≠ tc l
  hbc : ∀ l, tb l ≠ tc l
  sep : ∀ l l' e, e ∈ tri3 (ta l) (tb l) (tc l) → e ∈ tri3 (ta l') (tb l') (tc l') → l = l'

variable {ta tb tc}

theorem GoodLabels.isDecomp (h : GoodLabels ta tb tc) :
    IsDecomp part1 triFam (labelEdges ta tb tc) (labelTris ta tb tc) := by
  have htri : ∀ l, triEdges ({ta l, tb l, tc l} : Finset W) = tri3 (ta l) (tb l) (tc l) :=
    fun l => triEdges_three (h.hab l) (h.hac l) (h.hbc l)
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨l, -, rfl⟩ := mem_image.mp hs
    refine ⟨card_three (h.hab l) (h.hac l) (h.hbc l), ?_⟩
    rw [map_three part1 (h.hab l) (h.hac l) (h.hbc l)]
    simp [triFam, part1]
  · intro s hs s' hs' hne
    obtain ⟨l, -, rfl⟩ := mem_image.mp (mem_coe.mp hs)
    obtain ⟨l', -, rfl⟩ := mem_image.mp (mem_coe.mp hs')
    simp only [Function.onFun, htri]
    rw [Finset.disjoint_left]
    intro e he he'
    exact hne (by rw [h.sep l l' e he he'])
  · rw [labelTris, image_biUnion, labelEdges]
    exact biUnion_congr rfl fun l _ => htri l

theorem GoodLabels.hasDecomp (h : GoodLabels ta tb tc) :
    HasDecomp part1 triFam (labelEdges ta tb tc) :=
  ⟨_, h.isDecomp⟩

theorem GoodLabels.card_labelEdges (h : GoodLabels ta tb tc) :
    (labelEdges ta tb tc).card = 3 * Fintype.card L := by
  rw [labelEdges, card_biUnion]
  · rw [sum_congr rfl fun l _ => card_tri3 (h.hab l) (h.hac l) (h.hbc l)]
    simp [mul_comm]
  · intro l _ l' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    exact fun e he he' => hne (h.sep l l' e he he')

theorem mem_labelEdges {e : Sym2 W} :
    e ∈ labelEdges ta tb tc ↔ ∃ l, e ∈ tri3 (ta l) (tb l) (tc l) := by
  simp [labelEdges]

end Labels

/-! ### Edges given by positions -/

section Positions

variable {I : Type*} [Fintype I]

/-- The edge set `{a i b i}` indexed by positions. -/
def posEdges (a b : I → W) : Finset (Sym2 W) := univ.image fun i => s(a i, b i)

theorem mem_posEdges {a b : I → W} {e : Sym2 W} :
    e ∈ posEdges a b ↔ ∃ i, e = s(a i, b i) := by
  simp [posEdges, eq_comm]

theorem card_posEdges {a b : I → W} (h : Function.Injective fun i => s(a i, b i)) :
    (posEdges a b).card = Fintype.card I := by
  rw [posEdges, card_image_of_injective _ h, card_univ]

omit [Fintype I] in
/-- **Subdivision block.** For position edges `a i b i` and fresh middles `c i`, the edge
set `{a b} ∪ {a c} ∪ {c b}` is decomposed by the triangles `a b c`. -/
theorem goodLabels_subdivision (a b c : I → W)
    (hab : ∀ i, a i ≠ b i) (hinj : Function.Injective fun i => s(a i, b i))
    (hc : Function.Injective c) (hca : ∀ i j, c i ≠ a j) (hcb : ∀ i j, c i ≠ b j) :
    GoodLabels a b c := by
  refine ⟨hab, fun i h => hca i i h.symm, fun i h => hcb i i h.symm, ?_⟩
  intro l l' e he he'
  rw [mem_tri3] at he he'
  rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h <;>
    first
    | exact hinj h
    | (simp only [Sym2.eq_iff] at h
       rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
       first
       | exact hc h1 | exact hc h2 | exact hc h1.symm | exact hc h2.symm
       | exact absurd h1 (hca _ _) | exact absurd h1.symm (hca _ _)
       | exact absurd h1 (hcb _ _) | exact absurd h1.symm (hcb _ _)
       | exact absurd h2 (hca _ _) | exact absurd h2.symm (hca _ _)
       | exact absurd h2 (hcb _ _) | exact absurd h2.symm (hcb _ _))

theorem labelEdges_subdivision (a b c : I → W) :
    labelEdges a b c = posEdges a b ∪ (posEdges a c ∪ posEdges c b) := by
  ext e
  simp only [mem_labelEdges, mem_union, mem_posEdges, mem_tri3]
  constructor
  · rintro ⟨i, rfl | rfl | rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr (Or.inl ⟨i, rfl⟩)
    · exact Or.inr (Or.inr ⟨i, Sym2.eq_swap⟩)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr (Or.inl rfl)⟩
    · exact ⟨i, Or.inr (Or.inr Sym2.eq_swap)⟩

/-- `H ∪ ∇H` is triangle-decomposable. -/
theorem hasDecomp_subdivision (a b c : I → W)
    (hab : ∀ i, a i ≠ b i) (hinj : Function.Injective fun i => s(a i, b i))
    (hc : Function.Injective c) (hca : ∀ i j, c i ≠ a j) (hcb : ∀ i j, c i ≠ b j) :
    HasDecomp part1 triFam (posEdges a b ∪ (posEdges a c ∪ posEdges c b)) := by
  rw [← labelEdges_subdivision]
  exact (goodLabels_subdivision a b c hab hinj hc hca hcb).hasDecomp


/-- Degree of a vertex in an edge set given by positions. -/
theorem incidentLoad_posEdges {a b : I → W}
    (hinj : Function.Injective fun i => s(a i, b i)) (hne : ∀ i, a i ≠ b i) (z : W) :
    AntiEdgeSelection.incidentLoad (posEdges a b) z =
      (univ.filter fun i => a i = z).card + (univ.filter fun i => b i = z).card := by
  classical
  have hfil : (posEdges a b).filter (fun e => z ∈ e) =
      ((univ.filter fun i => a i = z) ∪ (univ.filter fun i => b i = z)).image
        fun i => s(a i, b i) := by
    rw [posEdges, filter_image]
    congr 1
    ext i
    simp [eq_comm]
  have hdisj : Disjoint (univ.filter fun i => a i = z) (univ.filter fun i => b i = z) := by
    rw [disjoint_filter]
    intro i _ h1 h2
    exact hne i (h1.trans h2.symm)
  unfold AntiEdgeSelection.incidentLoad
  rw [hfil, card_image_of_injOn hinj.injOn, card_union_of_disjoint hdisj]

/-- Precomposing with a permutation does not change a fibre count. -/
theorem card_filter_perm (σ : Equiv.Perm I) (f : I → W) (z : W) :
    (univ.filter fun i => f (σ i) = z).card = (univ.filter fun i => f i = z).card := by
  apply card_bij (fun i _ => σ i)
  · intro i hi; simpa using hi
  · intro i _ j _ hij; exact σ.injective hij
  · intro j hj
    exact ⟨σ.symm j, by simpa using hj, by simp⟩

end Positions

end PartitionedTriangleAbsorption.PrivateTemplate
