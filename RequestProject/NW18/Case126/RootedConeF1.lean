/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.CrossingCoverF1

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: the ROOTED cone, a necessary invariant of every vortex level (new)

`F1_rooted_cone` (proved): in every `F₁`-decomposable edge set, at every vertex `x` of class `c`,
the number of neighbours of class `c` is at most the number of neighbours in the two partner
classes of `c`.  (Every `F₁` triangle through `x` has at most one other vertex of class `c`, and
if it has one, its third vertex is a partner; a finite check, `F1_link_weight`.)

`cover_down_needs_cone` (proved): if `D ⊆ E(H)` is `F₁`-decomposable and every edge of `H` outside
`D` lies inside `U`, then every vertex `x ∉ U` satisfies the rooted cone in `H` itself.

**Consequence for `CrossingCover.F1VortexCoverDown`.**  Its hypotheses only ask that every class
has at least a fifth of `W`; they allow `|W_0| = 2|W|/5`, `|W_2| = |W_3| = |W|/5`, where the cone
at a class-`0` vertex is TIGHT (`|W_0| = |W_2| + |W_3|`), and a damage of `ζ |W|` partner edges at
one vertex `x ∈ W \ U` then violates the cone at `x`; by `cover_down_needs_cone` no `D` exists for
such an `H` (whenever it also satisfies the remaining hypotheses — we did not formalize a concrete
integrally divisible instance).  The degree budget alone therefore does not determine feasibility:
the missing invariant is a **rooted cone slack**, which at set level is
`ClassConeSlack p S θ : |S_c| + θ |S| ≤ |S_{d₁(c)}| + |S_{d₂(c)}|` for `S = W, U, U'`.  It is
preserved by the level (it is a property of the nested vertex sets, not of the damaged graph), and
with `θ > ξ + ζ` it implies the cone with slack at every vertex of every level.  The corrected
level statement `F1VortexCoverDownCone` (in `VortexSupplyF1.lean`) carries it explicitly.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption CrossingCover
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Finite check: in an `F₁` triangle `{c, i, j}`, the class-`c` count among `i, j` is at most the
partner count. -/
lemma F1_link_weight : ∀ c i j : Fin 4, ({c, i, j} : Multiset (Fin 4)) ∈ F1 →
    (if i = c then 1 else 0) + (if j = c then 1 else 0) ≤
      (if i = partner1 c ∨ i = partner2 c then 1 else 0) +
        (if j = partner1 c ∨ j = partner2 c then 1 else 0) := by
  decide

omit [Fintype V] in
lemma card_filter_pair_ite (P : V → Prop) [DecidablePred P] {b d : V} (hbd : b ≠ d) :
    (({b, d} : Finset V).filter P).card = (if P b then 1 else 0) + (if P d then 1 else 0) := by
  rw [Finset.filter_insert, Finset.filter_singleton]
  split_ifs with h1 h2 h2 <;> simp [hbd]

/-- Neighbours of `x` along a triangle `t` with a property `P`. -/
lemma tri_nbrs (P : V → Prop) [DecidablePred P] (t : Finset V) (x : V) :
    (univ.filter fun y => s(x, y) ∈ triEdges t ∧ P y) =
      if x ∈ t then (t.erase x).filter P else ∅ := by
  ext y
  simp only [mem_filter, mem_univ, true_and, triEdges, Finset.mk_mem_sym2_iff,
    Sym2.mk_isDiag_iff]
  split_ifs with hx
  · simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨⟨⟨-, hy⟩, hxy⟩, hP⟩; exact ⟨⟨fun h => hxy h.symm, hy⟩, hP⟩
    · rintro ⟨⟨hyx, hy⟩, hP⟩; exact ⟨⟨⟨hx, hy⟩, fun h => hyx h.symm⟩, hP⟩
  · simp only [Finset.notMem_empty, iff_false, not_and]
    intro h; exact absurd h.1.1 hx

/-- **The `F₁` rooted cone** (proved). -/
theorem F1_rooted_cone (p : V → Fin 4) (E : Finset (Sym2 V)) (h : HasDecomp p F1 E) (x : V) :
    (univ.filter fun y => s(x, y) ∈ E ∧ p y = p x).card ≤
      (univ.filter fun y => s(x, y) ∈ E ∧ (p y = partner1 (p x) ∨ p y = partner2 (p x))).card := by
  classical
  obtain ⟨D, hty, hdisj, rfl⟩ := h
  have hsum : ∀ (P : V → Prop) [DecidablePred P],
      (univ.filter fun y => s(x, y) ∈ D.biUnion triEdges ∧ P y).card =
        ∑ t ∈ D, (univ.filter fun y => s(x, y) ∈ triEdges t ∧ P y).card := by
    intro P _
    rw [← Finset.card_biUnion]
    · congr 1
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_biUnion]
      constructor
      · rintro ⟨⟨t, ht, he⟩, hP⟩; exact ⟨t, ht, he, hP⟩
      · rintro ⟨t, ht, he, hP⟩; exact ⟨⟨t, ht, he⟩, hP⟩
    · intro t ht t' ht' hne
      rw [Function.onFun, disjoint_left]
      intro y hy hy'
      simp only [mem_filter, mem_univ, true_and] at hy hy'
      exact disjoint_left.mp (hdisj ht ht' hne) hy.1 hy'.1
  rw [hsum, hsum]
  apply Finset.sum_le_sum
  intro t ht
  have h3 := (hty t ht).1
  rw [tri_nbrs _ t x, tri_nbrs _ t x]
  split_ifs with hx
  · have h2 : (t.erase x).card = 2 := by rw [card_erase_of_mem hx, h3]
    obtain ⟨b, d, hbd, hbde⟩ := Finset.card_eq_two.mp h2
    have hb : b ∈ t.erase x := by rw [hbde]; simp
    have hd : d ∈ t.erase x := by rw [hbde]; simp
    have hxb : x ≠ b := fun h => (mem_erase.mp hb).1 h.symm
    have hxd : x ≠ d := fun h => (mem_erase.mp hd).1 h.symm
    have ht' : t = {x, b, d} := by rw [← insert_erase hx, hbde]
    have htype := (hty t ht).2
    rw [ht', triple_val_map p hxb hxd hbd] at htype
    rw [hbde, card_filter_pair_ite _ hbd, card_filter_pair_ite _ hbd]
    exact F1_link_weight (p x) (p b) (p d) htype
  · simp

/-- **A cover-down level needs the rooted cone at every peeled vertex** (proved).  If
`D ⊆ E(H)` is `F₁`-decomposable and every edge of `H` outside `D` lies inside `U`, then at every
`x ∉ U` the `H`-neighbours of class `p x` are at most the `H`-neighbours of the partner classes. -/
theorem cover_down_needs_cone (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (D : Finset (Sym2 V)) (hDH : D ⊆ H.edgeFinset) (hD : HasDecomp p F1 D)
    (hrest : ∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) (x : V) (hx : x ∉ U) :
    (univ.filter fun y => H.Adj x y ∧ p y = p x).card ≤
      (univ.filter fun y => H.Adj x y ∧ (p y = partner1 (p x) ∨ p y = partner2 (p x))).card := by
  have hsame : ∀ y, H.Adj x y ↔ s(x, y) ∈ D := by
    intro y
    constructor
    · intro hxy
      by_contra hn
      exact hx (hrest _ (SimpleGraph.mem_edgeFinset.mpr hxy) hn x (Sym2.mem_mk_left _ _))
    · intro he
      exact SimpleGraph.mem_edgeFinset.mp (hDH he)
  simp_rw [hsame]
  exact F1_rooted_cone p D hD x

/-- Set-level rooted cone slack of the classes of `S`. -/
def ClassConeSlack (p : V → Fin 4) (S : Finset V) (θ : ℝ) : Prop :=
  ∀ c : Fin 4, ((S.filter fun z => p z = c).card : ℝ) + θ * S.card ≤
    (S.filter fun z => p z = partner1 c).card + (S.filter fun z => p z = partner2 c).card

end NashWilliams18.SpreadF1
