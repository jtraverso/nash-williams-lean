/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoherentTransformer.Target

/-! # The star (signed-link) obstruction to coherent transformers

Let `v` be a vertex and `sg : V → ℤ` a signing of its neighbours such that
`sg a + sg b = 0` whenever `v a b` is an `F`-typed triangle of `G`
(`LinkSigned`): for `sg = ±1` this says the F-link of `v` is bipartite.
Then the star charge `χ_v(va) = sg a` annihilates every `F`-typed triangle
of `G`. If `v` is a root of `Hx` but not a vertex of `Hy`, and the signed
`Hx`-degree of `v` is nonzero, NO physical transformer exists.

Equivalently, a necessary (obstruction-killing) condition for every
transformer is: for every root `v` of exactly one of the two trails and every
link signing `sg` at `v`, the signed trail-degree of `v` vanishes.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoherentTransformer

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

/-- The star charge at `v` with signing `sg`. -/
def starChargeOf (v : V) (sg : V → ℤ) : Sym2 V → ℤ :=
  Sym2.lift ⟨fun a b => (if a = v then sg b else 0) + (if b = v then sg a else 0),
    fun _ _ => add_comm _ _⟩

omit [Fintype V] in
theorem starChargeOf_mk (v : V) (sg : V → ℤ) (a b : V) :
    starChargeOf v sg s(a, b) = (if a = v then sg b else 0) + (if b = v then sg a else 0) :=
  rfl

/-- The signing `sg` is balanced on the `F`-link of `v` in `G`. -/
def LinkSigned (p : V → Fin t) (F : Finset (Multiset (Fin t))) (G : SimpleGraph V)
    (v : V) (sg : V → ℤ) : Prop :=
  ∀ a b, G.Adj v a → G.Adj v b → G.Adj a b →
    ({p v, p a, p b} : Multiset (Fin t)) ∈ F → sg a + sg b = 0

omit [Fintype V] [DecidableEq V] in
theorem triple_swap12 (p : V → Fin t) (a b c : V) :
    ({p a, p b, p c} : Multiset (Fin t)) = {p b, p a, p c} := by
  simp only [Multiset.insert_eq_cons]
  exact Multiset.cons_swap _ _ _

omit [Fintype V] [DecidableEq V] in
theorem triple_rot (p : V → Fin t) (a b c : V) :
    ({p a, p b, p c} : Multiset (Fin t)) = {p c, p a, p b} := by
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero]
  rw [Multiset.cons_swap (p b) (p c), Multiset.cons_swap (p a) (p c)]

/-- **A balanced link signing gives a triangle-annihilating star charge.** -/
theorem starChargeOf_annihilating {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {v : V} {sg : V → ℤ}
    (h : LinkSigned p F G v sg) : TriangleAnnihilating p F G (starChargeOf v sg) := by
  intro s ⟨hcard, hF⟩ hsub
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := card_eq_three.mp hcard
  rw [triEdges_three hab hac hbc] at hsub ⊢
  have hAB : G.Adj a b := by
    have := hsub (by simp : s(a, b) ∈ _); simpa using this
  have hAC : G.Adj a c := by
    have := hsub (by simp : s(a, c) ∈ _); simpa using this
  have hBC : G.Adj b c := by
    have := hsub (by simp : s(b, c) ∈ _); simpa using this
  have hval : ({a, b, c} : Finset V).val = {a, b, c} := by
    simp [Finset.insert_val, Multiset.ndinsert_of_notMem, hab, hac, hbc]
  rw [hval] at hF
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton] at hF
  simp only [← Multiset.insert_eq_cons] at hF
  have h1 : s(a, b) ∉ ({s(a, c), s(b, c)} : Finset (Sym2 V)) := by
    simp [hab, hac, hbc, Ne.symm hab]
  have h2 : s(a, c) ∉ ({s(b, c)} : Finset (Sym2 V)) := by
    simp [hab, hac, Ne.symm hbc]
  rw [sum_insert h1, sum_insert h2, sum_singleton, starChargeOf_mk, starChargeOf_mk,
    starChargeOf_mk]
  by_cases ha : a = v
  · subst ha
    simp only [Ne.symm hab, Ne.symm hac, ↓reduceIte, add_zero]
    have := h b c hAB hAC hBC hF
    omega
  by_cases hb : b = v
  · subst hb
    simp only [ha, Ne.symm hbc, ↓reduceIte, add_zero, zero_add]
    have := h a c (G.adj_symm hAB) hBC hAC (by rw [← triple_swap12]; exact hF)
    omega
  by_cases hc : c = v
  · subst hc
    simp only [ha, hb, ↓reduceIte, zero_add]
    have := h a b (G.adj_symm hAC) (G.adj_symm hBC) hAB (by rw [← triple_rot]; exact hF)
    omega
  simp [ha, hb, hc]

variable {I : Type*} [Fintype I]

omit [Fintype V] in
/-- The star charge at `v` vanishes on a trail that avoids `v`. -/
theorem starChargeOf_trail_avoid (σ : Equiv.Perm I) (y : I → V) (v : V) (sg : V → ℤ)
    (hv : ∀ i, y i ≠ v) : ∑ e ∈ trailEdges σ y, starChargeOf v sg e = 0 := by
  refine sum_eq_zero fun e he => ?_
  simp only [trailEdges, mem_image, mem_univ, true_and] at he
  obtain ⟨i, rfl⟩ := he
  simp [starChargeOf_mk, hv]

/-- **Star obstruction.** If the `F0`-link of a source root `v` admits a
balanced signing whose signed `Hx`-degree is nonzero, and `v` is not a vertex
of `Hy`, then no physical coherent transformer exists. -/
theorem no_transformer_of_star {p : V → Fin 2} {G : SimpleGraph V} [DecidableRel G.Adj]
    {σ : Equiv.Perm I} {x y : I → V} (hx : PhysicalTrail G σ x) (hy : PhysicalTrail G σ y)
    {v : V} {sg : V → ℤ} (hsg : LinkSigned p TypedApplicationLinks.F0 G v sg)
    (hv : ∀ i, y i ≠ v) (hne : ∑ e ∈ trailEdges σ x, starChargeOf v sg e ≠ 0)
    (T : Finset (Sym2 V)) : ¬ IsCoherentTransformer p G σ x y T := by
  rintro ⟨hT, hd, hdx, hdy⟩
  have h := charge_eq_of_transformer (starChargeOf_annihilating hsg) hT
    hx.trailEdges_subset hy.trailEdges_subset
    (disjoint_of_subset_right subset_union_left hd)
    (disjoint_of_subset_right subset_union_right hd) hdx hdy
  rw [starChargeOf_trail_avoid σ y v sg hv] at h
  exact hne h

end PartitionedTriangleAbsorption.CoherentTransformer
