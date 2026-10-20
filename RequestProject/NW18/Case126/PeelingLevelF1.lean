/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.CrossingCoverF1

@[expose] public section

/-!
# Theorem 14.7 for `F₁`, vortex route: one physical peeling level (produced)

Let `H` be an integrally `F₁`-divisible graph all of whose edges lie inside a vertex set `W`, and
let `X ⊆ W`, `U = W \ X`.  This file decomposes **every edge of `H` touching `X`** into physical
`F₁`-triangles, using only edges of `H`; the only edges inside `U` used form a graph of maximum
degree `≤ |X|`.  The three steps:

1. `F1_inner_cover` — every edge `xx'` inside `X` is covered greedily by a triangle `x x' u` with
   `u ∈ U` (uses crossing edges `xu, x'u`; at most `|X|` crossing edges per apex);
2. parity — the remaining graph is integrally divisible (`isIntDiv_sdiff_of_hasDecomp`) and the
   remaining edges at an apex `x` are exactly its crossing star, so `F1_degree_even_of_intDiv`
   gives the `F₁` link parity;
3. `CrossingCover.F1_crossing_cover` — all crossing stars are covered simultaneously by the dense
   typed link pairing (crossing load `≤ |X|`).

**What this is and is not.**  `F1_peeling_level` is a *producer* (no decomposition is supplied).
It performs ONE level of a cover-down.  Iterating it down to a bounded core deterministically is
impossible in general: the damage `≤ |X|` inside `U` accumulates over the levels.  The missing
ingredient is a spreading (random vortex) mechanism; see `NW18_BRANCH_LEDGER.md` §0quater.
-/

namespace NashWilliams18.CrossingCover

open Finset PartitionedTriangleAbsorption LinkPairing
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-! ### Degree parity from integral `F₁`-divisibility -/

lemma degVec_of_edgeSet_iff (p : V → Fin 4) (J : SimpleGraph V) [DecidableRel J.Adj]
    (E : Finset (Sym2 V)) (hJE : ∀ e, e ∈ J.edgeSet ↔ e ∈ E) (x : V) (j : Fin 4) :
    degVec p E x j = ((univ.filter fun w => J.Adj x w ∧ p w = j).card : ℤ) := by
  classical
  have hJ : J.edgeFinset = E := by
    ext e; rw [SimpleGraph.mem_edgeFinset]; exact hJE e
  rw [← hJ]
  exact PartitionedTriangleAbsorption.TypedLoadCounterexample.degVec_edgeFinset p J x j

/-- The degree vector of a loopless edge set counts neighbours by class. -/
lemma degVec_finset (p : V → Fin 4) (E : Finset (Sym2 V)) (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (x : V) (j : Fin 4) :
    degVec p E x j = ((univ.filter fun y => s(x, y) ∈ E ∧ p y = j).card : ℤ) := by
  classical
  rw [degVec_of_edgeSet_iff p (SimpleGraph.fromEdgeSet (E : Set (Sym2 V))) E (by
    intro e
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; exact ⟨h, hE e h⟩) x j]
  congr 2
  ext y
  simp only [mem_filter, mem_univ, true_and, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨h, -⟩, hj⟩; exact ⟨h, hj⟩
  · rintro ⟨h, hj⟩
    refine ⟨⟨h, fun hxy => hE _ h ?_⟩, hj⟩
    rw [hxy]; exact Sym2.mk_isDiag_iff.mpr rfl

/-- Every vertex degree vector of an `F₁` type has coordinate sum `2`. -/
lemma typeDegVec_sum_F1 : ∀ a : Fin 4, ∀ τ ∈ F1, a ∈ τ → ∑ i, typeDegVec τ a i = 2 := by
  decide

/-- **Degree parity from integral `F₁`-divisibility**: in an integrally `F₁`-divisible loopless
edge set every vertex has even degree. -/
theorem F1_degree_even_of_intDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F1 E) (x : V) :
    Even ((univ.filter fun y => s(x, y) ∈ E).card) := by
  classical
  obtain ⟨c, hc⟩ := hdiv.2 x
  have h1 : ∑ i, degVec p E x i = ((univ.filter fun y => s(x, y) ∈ E).card : ℤ) := by
    simp_rw [degVec_finset p E hE x]
    rw [← Nat.cast_sum]
    congr 1
    rw [card_eq_sum_card_fiberwise (f := p) (t := univ) (fun _ _ => mem_coe.mpr (mem_univ _))]
    refine sum_congr rfl fun i _ => ?_
    congr 1
    ext y
    simp
  have h2 : ∑ i, degVec p E x i = ∑ τ ∈ F1 with p x ∈ τ, c τ * 2 := by
    rw [hc]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [sum_comm]
    refine sum_congr rfl fun τ hτ => ?_
    rw [← mul_sum, typeDegVec_sum_F1 _ τ (mem_filter.mp hτ).1 (mem_filter.mp hτ).2]
  rw [h1] at h2
  have hev : Even (((univ.filter fun y => s(x, y) ∈ E).card : ℕ) : ℤ) :=
    ⟨∑ τ ∈ F1 with p x ∈ τ, c τ, by rw [h2, ← sum_add_distrib]; congr 1; ext; ring⟩
  exact (Int.even_coe_nat _).mp hev

/-! ### Step 1: the edges inside `X` -/

/-- The edges of `H` inside `X`. -/
def innerEdges (H : SimpleGraph V) [DecidableRel H.Adj] (X : Finset V) : Finset (Sym2 V) :=
  H.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ X

lemma mem_innerEdges {H : SimpleGraph V} [DecidableRel H.Adj] {X : Finset V} {e : Sym2 V}
    (he : e ∈ innerEdges H X) : ∃ a b, e = s(a, b) ∧ a ∈ X ∧ b ∈ X ∧ H.Adj a b := by
  induction e using Sym2.ind with
  | _ a b =>
    obtain ⟨h1, h2⟩ := mem_filter.mp he
    exact ⟨a, b, rfl, h2 a (Sym2.mem_mk_left _ _), h2 b (Sym2.mem_mk_right _ _),
      SimpleGraph.mem_edgeFinset.mp h1⟩

omit [Fintype V] in
/-- A single typed triangle is decomposable. -/
lemma hasDecomp_single (p : V → Fin 4) {t : Finset V} (ht : IsTypedTri p F1 t) :
    HasDecomp p F1 (triEdges t) :=
  ⟨{t}, by simpa using ht, by simp, by simp⟩

/-- **Step 1 (produced): greedy cover of the edges inside `X`.**  If every edge `xx'` of `H`
inside `X` has a third class `k` with `T_{p x, p x', k} ∈ F₁` and at least `2|X|+1` common
`H`-neighbours of class `k` in `U` (disjoint from `X`), then the edges of `H` inside `X` together
with a set `S` of crossing edges `x u` (`x ∈ X`, `u ∈ U`), at most `|X|` at each apex, are
`F₁`-decomposable. -/
theorem F1_inner_cover (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (X U : Finset V) (hXU : Disjoint X U)
    (hcommon : ∀ x ∈ X, ∀ x' ∈ X, H.Adj x x' → ∃ k : Fin 4,
      ({p x, p x', k} : Multiset (Fin 4)) ∈ F1 ∧
      2 * X.card + 1 ≤ (U.filter fun u => H.Adj x u ∧ H.Adj x' u ∧ p u = k).card) :
    ∃ S : Finset (Sym2 V), S ⊆ H.edgeFinset ∧
      (∀ e ∈ S, ∃ x ∈ X, ∃ u ∈ U, e = s(x, u)) ∧
      (∀ x ∈ X, (S.filter fun e => x ∈ e).card ≤ X.card) ∧
      HasDecomp p F1 (innerEdges H X ∪ S) := by
  classical
  suffices hL : ∀ L ⊆ innerEdges H X, ∃ S : Finset (Sym2 V), S ⊆ H.edgeFinset ∧
      (∀ e ∈ S, ∃ x ∈ X, ∃ u ∈ U, e = s(x, u)) ∧
      (∀ x ∈ X, (S.filter fun e => x ∈ e).card ≤ (X.filter fun y => s(x, y) ∈ L).card) ∧
      HasDecomp p F1 (L ∪ S) by
    obtain ⟨S, h1, h2, h3, h4⟩ := hL _ subset_rfl
    exact ⟨S, h1, h2, fun x hx => (h3 x hx).trans (card_filter_le _ _), h4⟩
  intro L
  induction L using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, empty_subset _, by simp, by simp, ⟨∅, by simp, by simp, by simp⟩⟩
  | insert e L heL ih =>
    intro hsub
    obtain ⟨S, hSG, hScross, hSdeg, hSdec⟩ := ih ((subset_insert _ _).trans hsub)
    obtain ⟨a, b, rfl, ha, hb, hab⟩ := mem_innerEdges (hsub (mem_insert_self _ _))
    obtain ⟨k, hk, hcount⟩ := hcommon a ha b hb hab
    -- the bad apexes
    have hbad : ∀ x ∈ X, ((U.filter fun u => s(x, u) ∈ S).card) ≤ X.card := by
      intro x hx
      refine le_trans ?_ ((hSdeg x hx).trans (card_filter_le _ _))
      refine card_le_card_of_injOn (fun u => s(x, u)) ?_ ?_
      · intro u hu
        exact mem_filter.mpr ⟨(mem_filter.mp hu).2, Sym2.mem_mk_left _ _⟩
      · intro u _ u' _ h
        exact Sym2.congr_right.mp h
    have hgood : ∃ u ∈ U, H.Adj a u ∧ H.Adj b u ∧ p u = k ∧ s(a, u) ∉ S ∧ s(b, u) ∉ S := by
      by_contra hno
      push_neg at hno
      have hsub2 : (U.filter fun u => H.Adj a u ∧ H.Adj b u ∧ p u = k) ⊆
          (U.filter fun u => s(a, u) ∈ S) ∪ (U.filter fun u => s(b, u) ∈ S) := by
        intro u hu
        obtain ⟨huU, h1, h2, h3⟩ := mem_filter.mp hu
        by_cases h : s(a, u) ∈ S
        · exact mem_union_left _ (mem_filter.mpr ⟨huU, h⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨huU, hno u huU h1 h2 h3 h⟩)
      have := (card_le_card hsub2).trans (card_union_le _ _)
      have := hbad a ha
      have := hbad b hb
      omega
    obtain ⟨u, huU, hau, hbu, hpu, hauS, hbuS⟩ := hgood
    have haX : a ∉ U := disjoint_left.mp hXU ha
    have hbX : b ∉ U := disjoint_left.mp hXU hb
    have hua : a ≠ u := fun h => haX (h ▸ huU)
    have hub : b ≠ u := fun h => hbX (h ▸ huU)
    have hab' : a ≠ b := hab.ne
    -- the new triangle
    have htyped : IsTypedTri p F1 ({a, b, u} : Finset V) := by
      refine ⟨?_, ?_⟩
      · rw [card_insert_of_notMem (by simp [hab', hua]), card_pair hub]
      · rw [triple_val_map p hab' hua hub, hpu]; exact hk
    have htri : triEdges ({a, b, u} : Finset V) = {s(a, b), s(a, u), s(b, u)} := by
      ext f
      rw [mem_triEdges_triple hab' hua hub]
      simp
    refine ⟨S ∪ {s(a, u), s(b, u)}, ?_, ?_, ?_, ?_⟩
    · refine union_subset hSG ?_
      intro f hf
      simp only [mem_insert, mem_singleton] at hf
      rcases hf with rfl | rfl
      · exact SimpleGraph.mem_edgeFinset.mpr hau
      · exact SimpleGraph.mem_edgeFinset.mpr hbu
    · intro f hf
      rcases mem_union.mp hf with hf | hf
      · exact hScross f hf
      · simp only [mem_insert, mem_singleton] at hf
        rcases hf with rfl | rfl
        · exact ⟨a, ha, u, huU, rfl⟩
        · exact ⟨b, hb, u, huU, rfl⟩
    · intro x hx
      have hxu : x ≠ u := fun h => disjoint_left.mp hXU hx (h ▸ huU)
      rw [filter_union]
      refine (card_union_le _ _).trans ?_
      have hS := hSdeg x hx
      -- contributions of the two new crossing edges at `x`
      have hnew : (({s(a, u), s(b, u)} : Finset (Sym2 V)).filter fun f => x ∈ f).card ≤
          (if x = a then 1 else 0) + (if x = b then 1 else 0) := by
        refine (card_le_card (s := _) (t := (if x = a then {s(a, u)} else ∅) ∪
          (if x = b then {s(b, u)} else ∅)) ?_).trans ((card_union_le _ _).trans ?_)
        · intro f hf
          obtain ⟨hf, hxf⟩ := mem_filter.mp hf
          simp only [mem_insert, mem_singleton] at hf
          rcases hf with rfl | rfl
          · rcases Sym2.mem_iff.mp hxf with h | h
            · simp [h]
            · exact absurd h hxu
          · rcases Sym2.mem_iff.mp hxf with h | h
            · simp [h]
            · exact absurd h hxu
        · split_ifs <;> simp
      have hgain : (X.filter fun y => s(x, y) ∈ L).card + (if x = a then 1 else 0) +
          (if x = b then 1 else 0) ≤ (X.filter fun y => s(x, y) ∈ insert s(a, b) L).card := by
        by_cases hxa : x = a
        · subst hxa
          have hxb : x ≠ b := hab'
          rw [if_pos rfl, if_neg hxb]
          have hb' : b ∉ X.filter fun y => s(x, y) ∈ L :=
            fun h => heL (mem_filter.mp h).2
          have : insert b (X.filter fun y => s(x, y) ∈ L) ⊆
              X.filter fun y => s(x, y) ∈ insert s(x, b) L := by
            intro y hy
            rcases mem_insert.mp hy with rfl | hy
            · exact mem_filter.mpr ⟨hb, mem_insert_self _ _⟩
            · exact mem_filter.mpr ⟨(mem_filter.mp hy).1, mem_insert_of_mem (mem_filter.mp hy).2⟩
          have := card_le_card this
          rw [card_insert_of_notMem hb'] at this
          omega
        · by_cases hxb : x = b
          · subst hxb
            rw [if_neg hxa, if_pos rfl]
            have ha' : a ∉ X.filter fun y => s(x, y) ∈ L := by
              intro h; apply heL; rw [Sym2.eq_swap]; exact (mem_filter.mp h).2
            have : insert a (X.filter fun y => s(x, y) ∈ L) ⊆
                X.filter fun y => s(x, y) ∈ insert s(a, x) L := by
              intro y hy
              rcases mem_insert.mp hy with rfl | hy
              · exact mem_filter.mpr ⟨ha, by rw [Sym2.eq_swap]; exact mem_insert_self _ _⟩
              · exact mem_filter.mpr ⟨(mem_filter.mp hy).1,
                  mem_insert_of_mem (mem_filter.mp hy).2⟩
            have := card_le_card this
            rw [card_insert_of_notMem ha'] at this
            omega
          · rw [if_neg hxa, if_neg hxb]
            refine card_le_card fun y hy => ?_
            exact mem_filter.mpr ⟨(mem_filter.mp hy).1, mem_insert_of_mem (mem_filter.mp hy).2⟩
      omega
    · -- glue the new triangle
      have hdisj : Disjoint (L ∪ S) (triEdges ({a, b, u} : Finset V)) := by
        rw [htri, disjoint_left]
        intro f hf hf'
        simp only [mem_insert, mem_singleton] at hf'
        rcases mem_union.mp hf with hfL | hfS
        · obtain ⟨c, d, rfl, hc, hd, -⟩ := mem_innerEdges (hsub (mem_insert_of_mem hfL))
          rcases hf' with h | h | h
          · exact heL (h ▸ hfL)
          · rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨rfl, -⟩
            · exact disjoint_left.mp hXU hd huU
            · exact disjoint_left.mp hXU hc huU
          · rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨rfl, -⟩
            · exact disjoint_left.mp hXU hd huU
            · exact disjoint_left.mp hXU hc huU
        · rcases hf' with rfl | rfl | rfl
          · obtain ⟨x, hx, w, hw, h⟩ := hScross _ hfS
            rcases Sym2.eq_iff.mp h with ⟨-, rfl⟩ | ⟨rfl, -⟩
            · exact disjoint_left.mp hXU hb hw
            · exact disjoint_left.mp hXU ha hw
          · exact hauS hfS
          · exact hbuS hfS
      have hfin := hSdec.union (hasDecomp_single p htyped) hdisj
      have heq : L ∪ S ∪ triEdges ({a, b, u} : Finset V) =
          insert s(a, b) L ∪ (S ∪ {s(a, u), s(b, u)}) := by
        rw [htri]
        ext f; simp only [mem_union, mem_insert, mem_singleton]; tauto
      rwa [heq] at hfin

/-! ### One peeling level -/

/-- The number of `H`-neighbours of `x` of class `j` inside `U`. -/
def nbrCount (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V) (x : V)
    (j : Fin 4) : ℕ :=
  (U.filter fun u => H.Adj x u ∧ p u = j).card

/-- The size margins of an apex `x` towards `U` (with defect `γ` and an extra loss `ℓ`). -/
def PeelMargins (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V)
    (x : V) (γ ℓ : ℕ) : Prop :=
  4 * γ + 1 + ℓ ≤ nbrCount p H U x (p x) ∧
  6 * γ + 1 + ℓ ≤ nbrCount p H U x (partner1 (p x)) ∧
  6 * γ + 1 + ℓ ≤ nbrCount p H U x (partner2 (p x)) ∧
  nbrCount p H U x (p x) + 8 * γ + 1 + ℓ ≤
    nbrCount p H U x (partner1 (p x)) + nbrCount p H U x (partner2 (p x))

/-- **One physical peeling level for `F₁`** (produced).  Let `H` be integrally `F₁`-divisible,
with all edges `F₁`-allowed and inside `X ∪ U` (`X, U` disjoint).  Assume:
* every edge inside `X` has a third class with `≥ 2|X|+1` common neighbours of that class in `U`;
* every `y ∈ U` has at most `γ₀` non-neighbours in `U` of every class allowed for it;
* every apex `x ∈ X` satisfies the margins `PeelMargins` with defect `γ₀ + |X|` and loss `|X|`.

Then there is `C ⊆ E(H)`, `F₁`-decomposable, containing every edge of `H` that meets `X`; the
edges of `C` inside `U` form a graph of maximum degree `≤ |X|`. -/
theorem F1_peeling_level (p : V → Fin 4) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hall : ∀ u v, H.Adj u v → AllowedT F1 (p u) (p v))
    (hdiv : IsIntDiv p F1 H.edgeFinset)
    (X U : Finset V) (hXU : Disjoint X U)
    (hHW : ∀ u v, H.Adj u v → u ∈ X ∨ u ∈ U)
    (γ₀ : ℕ)
    (hcommon : ∀ x ∈ X, ∀ x' ∈ X, H.Adj x x' → ∃ k : Fin 4,
      ({p x, p x', k} : Multiset (Fin 4)) ∈ F1 ∧
      2 * X.card + 1 ≤ (U.filter fun u => H.Adj x u ∧ H.Adj x' u ∧ p u = k).card)
    (hdense : ∀ y ∈ U, ∀ j : Fin 4, AllowedT F1 (p y) j →
      (U.filter fun z => p z = j ∧ ¬ H.Adj y z).card ≤ γ₀)
    (hmarg : ∀ x ∈ X, PeelMargins p H U x (γ₀ + X.card) X.card) :
    ∃ C ⊆ H.edgeFinset, HasDecomp p F1 C ∧
      (∀ e ∈ H.edgeFinset, e ∉ C → ∀ v ∈ e, v ∈ U) ∧
      ∀ v, ((C.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card ≤ X.card := by
  classical
  obtain ⟨S, hSH, hScross, hSdeg, hSdec⟩ := F1_inner_cover p H X U hXU hcommon
  set N : V → Finset V := fun x => U.filter fun u => H.Adj x u ∧ s(x, u) ∉ S with hNdef
  set E1 := H.edgeFinset \ (innerEdges H X ∪ S) with hE1
  have hE1sub : innerEdges H X ∪ S ⊆ H.edgeFinset := union_subset (filter_subset _ _) hSH
  have hE1div : IsIntDiv p F1 E1 := isIntDiv_sdiff_of_hasDecomp hdiv hSdec hE1sub
  have hE1diag : ∀ e ∈ E1, ¬ e.IsDiag := fun e he =>
    SimpleGraph.not_isDiag_of_mem_edgeSet H (SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1)
  -- the remaining edges at an apex are exactly its crossing star
  have hstarE1 : ∀ x ∈ X, (univ.filter fun y => s(x, y) ∈ E1) = N x := by
    intro x hx
    ext y
    simp only [mem_filter, mem_univ, true_and, hE1, mem_sdiff, mem_union, not_or,
      SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, hNdef]
    constructor
    · rintro ⟨hxy, hin, hS⟩
      refine ⟨?_, hxy, hS⟩
      rcases hHW y x hxy.symm with hyX | hyU
      · exact absurd (mem_filter.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hxy, by
          intro v hv; rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact hx
          · exact hyX⟩) hin
      · exact hyU
    · rintro ⟨hyU, hxy, hS⟩
      refine ⟨hxy, fun hin => ?_, hS⟩
      exact disjoint_left.mp hXU ((mem_filter.mp hin).2 y (Sym2.mem_mk_right _ _)) hyU
  -- class counts of the stars
  have hcount : ∀ x ∈ X, ∀ j : Fin 4,
      ((N x).filter fun y => p y = j).card ≤ nbrCount p H U x j ∧
      nbrCount p H U x j ≤ ((N x).filter fun y => p y = j).card +
        (U.filter fun u => p u = j ∧ s(x, u) ∈ S).card := by
    intro x hx j
    constructor
    · refine card_le_card fun u hu => ?_
      obtain ⟨hu, hj⟩ := mem_filter.mp hu
      obtain ⟨huU, hxu, -⟩ := mem_filter.mp hu
      exact mem_filter.mpr ⟨huU, hxu, hj⟩
    · refine (card_le_card (t := ((N x).filter fun y => p y = j) ∪
        (U.filter fun u => p u = j ∧ s(x, u) ∈ S)) ?_).trans (card_union_le _ _)
      intro u hu
      obtain ⟨huU, hxu, hj⟩ := mem_filter.mp hu
      by_cases hS : s(x, u) ∈ S
      · exact mem_union_right _ (mem_filter.mpr ⟨huU, hj, hS⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_filter.mpr ⟨huU, hxu, hS⟩, hj⟩)
  have hlost : ∀ x ∈ X, ∀ j₁ j₂ j₃ : Fin 4, j₁ ≠ j₂ → j₁ ≠ j₃ → j₂ ≠ j₃ →
      (U.filter fun u => p u = j₁ ∧ s(x, u) ∈ S).card +
        (U.filter fun u => p u = j₂ ∧ s(x, u) ∈ S).card +
        (U.filter fun u => p u = j₃ ∧ s(x, u) ∈ S).card ≤ X.card := by
    intro x hx j₁ j₂ j₃ h12 h13 h23
    have hd : ∀ a b : Fin 4, a ≠ b → Disjoint (U.filter fun u => p u = a ∧ s(x, u) ∈ S)
        (U.filter fun u => p u = b ∧ s(x, u) ∈ S) := by
      intro a b hab
      rw [disjoint_left]
      intro u hu hu'
      exact hab ((mem_filter.mp hu).2.1.symm.trans (mem_filter.mp hu').2.1)
    rw [← card_union_of_disjoint (hd _ _ h12), ← card_union_of_disjoint
      (disjoint_union_left.mpr ⟨hd _ _ h13, hd _ _ h23⟩)]
    refine le_trans ?_ (hSdeg x hx)
    refine card_le_card_of_injOn (fun u => s(x, u)) ?_ ?_
    · intro u hu
      have : s(x, u) ∈ S := by
        simp only [coe_union, Set.mem_union, mem_coe, mem_filter] at hu
        rcases hu with (h | h) | h <;> exact h.2.2
      exact mem_filter.mpr ⟨this, Sym2.mem_mk_left _ _⟩
    · intro u _ u' _ h
      exact Sym2.congr_right.mp h
  -- crossing cover of all stars
  have hNX : ∀ x ∈ X, ∀ y ∈ N x, y ∉ X := fun x _ y hy hyX =>
    disjoint_left.mp hXU hyX (mem_filter.mp hy).1
  have hstar : ∀ x ∈ X, ∀ y ∈ N x, H.Adj x y := fun x _ y hy => (mem_filter.mp hy).2.1
  have hcls : ∀ x ∈ X, ∀ y ∈ N x, p y = p x ∨ p y = partner1 (p x) ∨ p y = partner2 (p x) :=
    fun x hx y hy => allowed_F1_classes (p x) (p y) (hall x y (hstar x hx y hy))
  have hdense' : ∀ x ∈ X, ∀ y ∈ N x, ∀ j : Fin 4, LinkPair (p x) (p y) j →
      ((N x).filter fun z => p z = j ∧ ¬ (H.Adj y z ∧ s(y, z) ∉ (∅ : Finset (Sym2 V)))).card
        ≤ γ₀ := by
    intro x hx y hy j hj
    refine le_trans (card_le_card fun z hz => ?_) (hdense y (mem_filter.mp hy).1 j
      (linkPair_allowed _ _ _ hj))
    obtain ⟨hzN, hzj, hbad⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨(mem_filter.mp hzN).1, hzj, fun h => hbad ⟨h, notMem_empty _⟩⟩
  have hload : ∀ y, crossLoad X N y ≤ X.card := fun y => card_filter_le _ _
  have hmarg' : ∀ x ∈ X, LinkMargins p x (N x) (γ₀ + X.card) := by
    intro x hx
    obtain ⟨m1, m2, m3, m4⟩ := hmarg x hx
    obtain ⟨hc1, hc2, h12⟩ := partner_ne (p x)
    have l := hlost x hx (p x) (partner1 (p x)) (partner2 (p x)) hc1 hc2 h12
    obtain ⟨c0, c0'⟩ := hcount x hx (p x)
    obtain ⟨c1, c1'⟩ := hcount x hx (partner1 (p x))
    obtain ⟨c2, c2'⟩ := hcount x hx (partner2 (p x))
    -- parity
    have hev := F1_degree_even_of_intDiv p E1 hE1diag hE1div x
    rw [hstarE1 x hx] at hev
    have hsplit : N x = ((N x).filter fun y => p y = p x) ∪
        ((N x).filter fun y => p y = partner1 (p x)) ∪
        ((N x).filter fun y => p y = partner2 (p x)) := by
      ext y
      simp only [mem_union, mem_filter]
      constructor
      · intro hy
        rcases hcls x hx y hy with h | h | h
        · exact Or.inl (Or.inl ⟨hy, h⟩)
        · exact Or.inl (Or.inr ⟨hy, h⟩)
        · exact Or.inr ⟨hy, h⟩
      · rintro ((⟨hy, -⟩ | ⟨hy, -⟩) | ⟨hy, -⟩) <;> exact hy
    have hdc : ∀ a b : Fin 4, a ≠ b → Disjoint ((N x).filter fun y => p y = a)
        ((N x).filter fun y => p y = b) := by
      intro a b hab
      rw [disjoint_left]
      intro u hu hu'
      exact hab ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hu').2)
    rw [hsplit, card_union_of_disjoint (disjoint_union_left.mpr ⟨hdc _ _ hc2, hdc _ _ h12⟩),
      card_union_of_disjoint (hdc _ _ hc1)] at hev
    obtain ⟨r, hr⟩ := hev
    refine ⟨by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨M, hMH, -, hMv, hMdeg, hcross⟩ :=
    F1_crossing_cover p H ∅ X N γ₀ X.card hNX hstar hcls hdense' hload hmarg'
  refine ⟨innerEdges H X ∪ S ∪ (X.biUnion (fun x => star x (N x)) ∪ M), ?_, ?_, ?_, ?_⟩
  · refine union_subset hE1sub (union_subset ?_ hMH)
    intro e he
    obtain ⟨x, hx, he⟩ := mem_biUnion.mp he
    obtain ⟨y, hy, rfl⟩ := mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (hstar x hx y hy)
  · refine hSdec.union hcross ?_
    rw [disjoint_left]
    intro e he he'
    rcases mem_union.mp he with hin | hS
    · obtain ⟨a, b, rfl, ha, hb, -⟩ := mem_innerEdges hin
      rcases mem_union.mp he' with hst | hM
      · obtain ⟨x, hx, hst⟩ := mem_biUnion.mp hst
        obtain ⟨y, hy, heq⟩ := mem_image.mp hst
        have hyab : y ∈ s(a, b) := heq ▸ Sym2.mem_mk_right _ _
        rcases Sym2.mem_iff.mp hyab with rfl | rfl
        · exact hNX x hx _ hy ha
        · exact hNX x hx _ hy hb
      · exact (hMv _ hM a (Sym2.mem_mk_left _ _)).1 ha
    · obtain ⟨x, hx, u, -, rfl⟩ := hScross e hS
      rcases mem_union.mp he' with hst | hM
      · obtain ⟨x', hx', hst⟩ := mem_biUnion.mp hst
        obtain ⟨y, hy, heq⟩ := mem_image.mp hst
        exact (mem_filter.mp hy).2.2 (heq ▸ hS)
      · exact (hMv _ hM x (Sym2.mem_mk_left _ _)).1 hx
  · intro e he heC
    induction e using Sym2.ind with
    | _ a b =>
      have hab := SimpleGraph.mem_edgeFinset.mp he
      have key : ∀ a b : V, H.Adj a b → s(a, b) ∉
          innerEdges H X ∪ S ∪ (X.biUnion (fun x => star x (N x)) ∪ M) → a ∉ X := by
        intro a b hab hnot haX
        apply hnot
        rcases hHW b a hab.symm with hbX | hbU
        · refine mem_union_left _ (mem_union_left _ (mem_filter.mpr
            ⟨SimpleGraph.mem_edgeFinset.mpr hab, ?_⟩))
          intro v hv; rcases Sym2.mem_iff.mp hv with rfl | rfl
          · exact haX
          · exact hbX
        · by_cases hS : s(a, b) ∈ S
          · exact mem_union_left _ (mem_union_right _ hS)
          · refine mem_union_right _ (mem_union_left _ (mem_biUnion.mpr ⟨a, haX, ?_⟩))
            exact mem_image.mpr ⟨b, mem_filter.mpr ⟨hbU, hab, hS⟩, rfl⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · rcases hHW v b hab with h | h
        · exact absurd h (key v b hab heC)
        · exact h
      · rcases hHW v a hab.symm with h | h
        · exact absurd h (key v a hab.symm (by rw [Sym2.eq_swap]; exact heC))
        · exact h
  · intro v
    refine le_trans (card_le_card fun e he => ?_) ((hMdeg v).trans (hload v))
    obtain ⟨he, hve⟩ := mem_filter.mp he
    obtain ⟨heC, hU⟩ := mem_filter.mp he
    refine mem_filter.mpr ⟨?_, hve⟩
    rcases mem_union.mp heC with h | h
    · rcases mem_union.mp h with hin | hS
      · obtain ⟨a, b, rfl, ha, -, -⟩ := mem_innerEdges hin
        exact absurd (hU a (Sym2.mem_mk_left _ _)) (disjoint_left.mp hXU ha)
      · obtain ⟨x, hx, u, -, rfl⟩ := hScross _ hS
        exact absurd (hU x (Sym2.mem_mk_left _ _)) (disjoint_left.mp hXU hx)
    · rcases mem_union.mp h with hst | hM
      · obtain ⟨x, hx, hst⟩ := mem_biUnion.mp hst
        obtain ⟨y, -, rfl⟩ := mem_image.mp hst
        exact absurd (hU x (Sym2.mem_mk_left _ _)) (disjoint_left.mp hXU hx)
      · exact hM

end NashWilliams18.CrossingCover
