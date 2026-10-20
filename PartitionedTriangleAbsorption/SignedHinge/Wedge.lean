/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SignedHinge.Groups
public import Mathlib.Data.Finset.Sym

/-! # Small wedge, copy and vertex-set lemmas used by the signed hinge absorber

Generic in the type family `F`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SignedHinge

open Finset

variable {V : Type*} [DecidableEq V] {t : ℕ} {p : V → Fin t} {F : Finset (Multiset (Fin t))}

/-- Two triangles on a common edge `uv` with distinct apices `w, z`: the edges of the first
that are not in the second form the wedge `{uw, vw}`. -/
theorem triEdges_sdiff_apex {u v w z : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (huz : u ≠ z) (hvz : v ≠ z) (hwz : w ≠ z) :
    triEdges ({u, v, w} : Finset V) \ triEdges {u, v, z} = {s(u, w), s(v, w)} := by
  rw [triEdges_three huv huw hvw, triEdges_three huv huz hvz]
  ext e
  simp only [mem_sdiff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨h1 | h1 | h1, h2⟩
    · exact absurd (Or.inl h1) h2
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (rfl | rfl)
    · refine ⟨Or.inr (Or.inl rfl), ?_⟩
      simp only [Sym2.eq_iff, not_or, not_and]
      aesop
    · refine ⟨Or.inr (Or.inr rfl), ?_⟩
      simp only [Sym2.eq_iff, not_or, not_and]
      aesop

/-- The vertex triple of a triangle depends only on its base edge. -/
theorem triple_eq_of_sym2_eq {u v u' v' : V} (w : V) (h : s(u, v) = s(u', v')) :
    ({u, v, w} : Finset V) = {u', v', w} := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact insert_comm _ _ _

/-- The wedge at apex `w` depends only on its base edge. -/
theorem wedge_eq_of_sym2_eq {u v u' v' : V} (w : V) (h : s(u, v) = s(u', v')) :
    ({s(u, w), s(v, w)} : Finset (Sym2 V)) = {s(u', w), s(v', w)} := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact pair_comm _ _

omit [DecidableEq V] in
/-- An `F`-copy from three adjacencies and a type. -/
theorem isCopy_three {G : SimpleGraph V} [DecidableEq V] {a b c : V} (hab : G.Adj a b)
    (hac : G.Adj a c) (hbc : G.Adj b c) (hF : ({a, b, c} : Finset V).val.map p ∈ F) :
    IsCopy p F G {a, b, c} :=
  ⟨SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩, hF⟩

variable [Fintype V]

theorem mem_vertSet {E : Finset (Sym2 V)} {x : V} : x ∈ vertSet E ↔ ∃ e ∈ E, x ∈ e := by
  simp [vertSet]

theorem vertSet_mono {E₁ E₂ : Finset (Sym2 V)} (h : E₁ ⊆ E₂) : vertSet E₁ ⊆ vertSet E₂ := by
  intro x hx
  obtain ⟨e, he, hxe⟩ := mem_vertSet.mp hx
  exact mem_vertSet.mpr ⟨e, h he, hxe⟩

theorem vertSet_union (E₁ E₂ : Finset (Sym2 V)) :
    vertSet (E₁ ∪ E₂) = vertSet E₁ ∪ vertSet E₂ := by
  ext x
  simp only [mem_union, mem_vertSet]
  constructor
  · rintro ⟨e, he | he, hx⟩
    · exact Or.inl ⟨e, he, hx⟩
    · exact Or.inr ⟨e, he, hx⟩
  · rintro (⟨e, he, hx⟩ | ⟨e, he, hx⟩)
    · exact ⟨e, Or.inl he, hx⟩
    · exact ⟨e, Or.inr he, hx⟩

theorem vertSet_pair (x y : V) : vertSet ({s(x, y)} : Finset (Sym2 V)) = {x, y} := by
  ext v; simp [mem_vertSet]

/-- At most two vertices per edge. -/
theorem card_vertSet_le (E : Finset (Sym2 V)) : (vertSet E).card ≤ 2 * E.card := by
  induction E using Finset.induction_on with
  | empty => simp [vertSet]
  | insert e E he ih =>
    rw [card_insert_of_notMem he, insert_eq, vertSet_union]
    induction e using Sym2.ind with
    | _ x y =>
      rw [vertSet_pair]
      refine (card_union_le _ _).trans ?_
      have : ({x, y} : Finset V).card ≤ 2 := card_le_two
      omega

/-- An edge set has at most `C(|vertSet E| + 1, 2)` edges. -/
theorem card_le_choose_vertSet (E : Finset (Sym2 V)) :
    E.card ≤ Nat.choose ((vertSet E).card + 1) 2 := by
  rw [← card_sym2]
  refine card_le_card fun e he => ?_
  induction e using Sym2.ind with
  | _ x y =>
    rw [mk_mem_sym2_iff]
    exact ⟨mem_vertSet.mpr ⟨_, he, Sym2.mem_mk_left x y⟩,
      mem_vertSet.mpr ⟨_, he, Sym2.mem_mk_right x y⟩⟩

end PartitionedTriangleAbsorption.SignedHinge
