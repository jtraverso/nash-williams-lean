/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CoverDownBasicStage105

/-! # Stage105 cover-down, step 2: pairing the leftover stars through reserve triples

`M0` is a set of spokes (one end outside `U`) whose star at every outer vertex
has even size. Two spokes `xy₁, xy₂` of the same outer vertex are covered by one
reserve triple `(x, z, z')`: the actual triangles `x y₁ z` and `x z' y₂` use the
reserve spokes `xz, xz'` and two new internal edges `y₁z, z'y₂` inside `U`.
The internal edge `zz'` of a used triple is left inside `U`.

The only premises are the explicit pair richness `a2` of the reserve, counted
through edges outside the static forbidden set `B0 ⊇` reserve edges, and the
quantitative budget `m + 4λ ≤ 2 a2`, where `λ` bounds only the DYNAMIC load
`deg_{M0} + deg_{reserve}` at inner vertices (the static forbidden set may be
dense, e.g. contain every edge inside the next-but-one vortex set).
The new internal edges are charged: at every vertex their degree is at most
the `M0`-degree plus the used-spoke degree.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CoverDownStage105

open Finset TypedApplicationLinks AntiEdgeSelection

variable {V : Type*} [DecidableEq V]

/-- The fixed data of the pairing step. -/
structure PairingData (p : V → Fin 4) (E : Finset (Sym2 V)) (U : Finset V)
    (T2 : Finset (V × V × V)) (B0 M0 : Finset (Sym2 V)) (m lam a2 : ℕ) : Prop where
  cross : ∀ a b, s(a, b) ∈ E → p a ≠ p b
  res : ∀ r ∈ T2, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E
  res_disj : (T2 : Set (V × V × V)).PairwiseDisjoint resTri
  sub : M0 ⊆ E
  spoke : ∀ e ∈ M0, IsSpoke U e
  disj : Disjoint M0 (resEdges T2)
  forb : resEdges T2 ⊆ B0
  rich : ∀ x, x ∉ U → ∀ y₁ y₂, y₁ ≠ y₂ → s(x, y₁) ∈ M0 → s(x, y₂) ∈ M0 →
    a2 ≤ (T2.filter fun r => r.1 = x ∧ s(y₁, r.2.1) ∈ E ∧ s(r.2.2, y₂) ∈ E ∧
      s(y₁, r.2.1) ∉ B0 ∧ s(r.2.2, y₂) ∉ B0).card
  degM : ∀ x, x ∉ U → incidentLoad M0 x ≤ m
  loadB : ∀ y ∈ U, incidentLoad M0 y + incidentLoad (resEdges T2) y ≤ lam
  budget : m + 4 * lam ≤ 2 * a2

/-- The state invariant of the pairing induction. -/
structure PairingInv (E : Finset (Sym2 V)) (U : Finset V) (T2 : Finset (V × V × V))
    (B0 M0 : Finset (Sym2 V)) (M : Finset (Sym2 V)) (A : Finset (V × V × V))
    (I : Finset (Sym2 V)) : Prop where
  sub : M ⊆ M0
  resA : A ⊆ T2
  even : ∀ x, x ∉ U → Even (incidentLoad M x)
  count : ∀ x, x ∉ U → 2 * (A.filter fun r => r.1 = x).card + incidentLoad M x ≤ incidentLoad M0 x
  load : ∀ w, incidentLoad I w + incidentLoad M w ≤ incidentLoad M0 w + incidentLoad (spokesOf A) w
  inE : I ⊆ E
  inner : ∀ e ∈ I, IsInner U e
  avoid : Disjoint I B0

omit [DecidableEq V] in
theorem spoke_eq_of_mem {U : Finset V} {x : V} (hx : x ∉ U) {e : Sym2 V}
    (he : IsSpoke U e) (hxe : x ∈ e) : ∃ y, y ∈ U ∧ e = s(x, y) := by
  obtain ⟨a, b, ha, hb, rfl⟩ := he
  rcases Sym2.mem_iff.mp hxe with rfl | rfl
  · exact ⟨b, hb, rfl⟩
  · exact absurd hb hx

theorem incidentLoad_filter_A (A : Finset (V × V × V)) {r : V × V × V} (hr : r ∉ A) (x : V) :
    ((insert r A).filter fun q => q.1 = x).card =
      (A.filter fun q => q.1 = x).card + if r.1 = x then 1 else 0 := by
  rw [filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (fun h' => hr (mem_filter.mp h').1)]
  · rfl

omit [DecidableEq V] in
theorem spoke_not_inner {U : Finset V} {e : Sym2 V} (h : IsSpoke U e) : ¬ IsInner U e := by
  obtain ⟨a, b, ha, -, rfl⟩ := h
  exact fun hin => ha (hin a (Sym2.mem_mk_left a b))

theorem incidentLoad_pair {e f : Sym2 V} (h : e ≠ f) (w : V) :
    incidentLoad {e, f} w = (if w ∈ e then 1 else 0) + if w ∈ f then 1 else 0 := by
  rw [incidentLoad_insert (by simpa using h), show ({f} : Finset (Sym2 V)) = insert f ∅ from rfl,
    incidentLoad_insert (notMem_empty f), OnePart.incidentLoad_empty]
  omega

theorem spokesOf_insert (A : Finset (V × V × V)) (r : V × V × V) :
    spokesOf (insert r A) = resSpokes r ∪ spokesOf A := biUnion_insert

/-- Bounded first-coordinate collisions: the reserve triples at `x` whose first inner
vertex is joined to `y` by an edge of `S` number at most `deg_S(y)`. -/
theorem card_bad₁_le {T2 : Finset (V × V × V)}
    (hdisj : (T2 : Set (V × V × V)).PairwiseDisjoint resTri) (S : Finset (Sym2 V)) (x y : V) :
    (T2.filter fun r => r.1 = x ∧ s(y, r.2.1) ∈ S).card ≤ incidentLoad S y := by
  apply card_le_card_of_injOn (fun r => s(y, r.2.1))
  · intro r hr
    exact mem_filter.mpr ⟨(mem_filter.mp hr).2.2, Sym2.mem_mk_left _ _⟩
  · intro r hr r' hr' h
    have hr1 := mem_filter.mp hr
    have hr1' := mem_filter.mp hr'
    apply reserve_eq_of_fst hdisj hr1.1 hr1'.1 (hr1.2.1.trans hr1'.2.1.symm)
    rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, h2⟩
    · exact h2
    · exact h2.trans h1

theorem card_bad₂_le {T2 : Finset (V × V × V)}
    (hdisj : (T2 : Set (V × V × V)).PairwiseDisjoint resTri) (S : Finset (Sym2 V)) (x y : V) :
    (T2.filter fun r => r.1 = x ∧ s(r.2.2, y) ∈ S).card ≤ incidentLoad S y := by
  apply card_le_card_of_injOn (fun r => s(r.2.2, y))
  · intro r hr
    exact mem_filter.mpr ⟨(mem_filter.mp hr).2.2, Sym2.mem_mk_right _ _⟩
  · intro r hr r' hr' h
    have hr1 := mem_filter.mp hr
    have hr1' := mem_filter.mp hr'
    apply reserve_eq_of_snd hdisj hr1.1 hr1'.1 (hr1.2.1.trans hr1'.2.1.symm)
    rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exact h1.trans h2

end PartitionedTriangleAbsorption.CoverDownStage105
