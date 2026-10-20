/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReturnedBridge

/-! # Triangle-annihilating charges are transformer invariants

If an edge functional `χ` vanishes on every `F`-typed triangle of the host
`G`, then it vanishes on every `F`-decomposable edge set inside `E(G)`.
Consequently a physical transformer `T` for `Hx` and `Hy`, with `T`
edge-disjoint from both, forces `χ(Hx) = χ(Hy)`. This is a necessary
condition; it is not a construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoherentTransformer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The edge functional `χ` vanishes on every `F`-typed triangle of `G`. -/
def TriangleAnnihilating (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (χ : Sym2 V → ℤ) : Prop :=
  ∀ s : Finset V, IsTypedTri p F s → triEdges s ⊆ G.edgeFinset →
    ∑ e ∈ triEdges s, χ e = 0

theorem charge_eq_zero_of_hasDecomp {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {χ : Sym2 V → ℤ}
    (hχ : TriangleAnnihilating p F G χ) {E : Finset (Sym2 V)}
    (hE : E ⊆ G.edgeFinset) (h : HasDecomp p F E) : ∑ e ∈ E, χ e = 0 := by
  obtain ⟨D, hD, hdisj, hU⟩ := h
  subst hU
  rw [sum_biUnion hdisj]
  refine sum_eq_zero fun s hs => hχ s (hD s hs) ?_
  exact (subset_biUnion_of_mem triEdges hs).trans hE

/-- **Charge invariance.** Any physical transformer between `Hx` and `Hy`
equalises every triangle-annihilating charge. -/
theorem charge_eq_of_transformer {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {χ : Sym2 V → ℤ}
    (hχ : TriangleAnnihilating p F G χ) {T Hx Hy : Finset (Sym2 V)}
    (hT : T ⊆ G.edgeFinset) (hHx : Hx ⊆ G.edgeFinset) (hHy : Hy ⊆ G.edgeFinset)
    (hdx : Disjoint T Hx) (hdy : Disjoint T Hy)
    (hx : HasDecomp p F (T ∪ Hx)) (hy : HasDecomp p F (T ∪ Hy)) :
    ∑ e ∈ Hx, χ e = ∑ e ∈ Hy, χ e := by
  have h1 := charge_eq_zero_of_hasDecomp hχ (union_subset hT hHx) hx
  have h2 := charge_eq_zero_of_hasDecomp hχ (union_subset hT hHy) hy
  rw [sum_union hdx] at h1
  rw [sum_union hdy] at h2
  omega

end PartitionedTriangleAbsorption.CoherentTransformer
