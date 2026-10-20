/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Stage215Adapter
import RequestProject.NW18.Case126.LinkPairing
import RequestProject.NW18.Case125.Pairing

/-!
# Theorem 14.7 for `F₁`, vortex route: the physical crossing cover (produced)

This file proves, with no supplied decomposition, the **crossing-cover** step of one level of an
`F₁` vortex: every apex `x` of a set `X` has a *crossing star* `N x` (a set of neighbours outside
`X`), and all crossing stars are covered **simultaneously** by edge-disjoint `F₁`-triangles
`{x, y, z}` whose third edges `yz` are fresh edges of `G` avoiding a forbidden set `B₀`.

* `F1_apex_cover` (one apex): from the dense typed link pairing `LinkPairing.link_pairing`
  (Hall's theorem), the star of `x` together with a matching `M` inside `N` is `F₁`-decomposable.
  The triangle types are `{c,c,d₁}`, `{c,c,d₂}`, `{c,d₁,d₁}`, `{c,d₂,d₂}` with
  `c = p x` and partners `d₁, d₂` (`{2,3}` if `c ∈ {0,1}`, `{0,1}` otherwise) — all in `F₁`
  (`linkPat_mem_F1`, a finite check).
* `F1_crossing_cover` (all apexes): greedy over the apexes; the inner edges already used are added
  to the forbidden set.  Since every apex uses a *matching*, the used inner edges have degree at
  most the crossing load `#{x ∈ X : y ∈ N x}` at each `y`; this load (`≤ γ₁`) is paid in the
  density budget `γ = γ₀ + γ₁`.

The constants are explicit: density defect `γ₀` w.r.t. `G` and `B₀`, crossing load `γ₁`, margins
`|N_c| ≥ 4γ+1`, `|N_{d₁}|, |N_{d₂}| ≥ 6γ+1`, `|N_{d₁}| + |N_{d₂}| ≥ |N_c| + 8γ + 1` and the parity
`|N_c| ≡ |N_{d₁}| + |N_{d₂}| (mod 2)` (the `F₁` degree-lattice condition at `x`, see
`F1_parity_of_intDiv`).

**What this is and is not.**  It is a *producer* of physical triangles (no coefficients).  It is
the third stage of a vortex level; the first stage (an approximate packing of the part of the
level outside the next vortex set, preserving the crossing reserve) and the random choice of the
deep vortex sets are **not** proved here (see `NW18_BRANCH_LEDGER.md` §0quater).
-/

namespace NashWilliams18.CrossingCover

open Finset PartitionedTriangleAbsorption LinkPairing
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

/-- First partner class of an apex class in the `F₁` link. -/
def partner1 (c : Fin 4) : Fin 4 := if c.val < 2 then 2 else 0

/-- Second partner class of an apex class in the `F₁` link. -/
def partner2 (c : Fin 4) : Fin 4 := if c.val < 2 then 3 else 1

lemma partner_ne : ∀ c : Fin 4, c ≠ partner1 c ∧ c ≠ partner2 c ∧ partner1 c ≠ partner2 c := by
  decide

/-- The four link pair types of an apex give `F₁`-triangles. -/
lemma linkPat_mem_F1 : ∀ c i j : Fin 4, LinkPat c (partner1 c) (partner2 c) i j →
    ({c, i, j} : Multiset (Fin 4)) ∈ F1 := by
  decide

/-- The classes `F₁`-allowed with `c` are `c` and its two partners. -/
lemma allowed_F1_classes : ∀ c j : Fin 4, AllowedT F1 c j →
    j = c ∨ j = partner1 c ∨ j = partner2 c := by
  decide

/-- `(i, j)` is a pair type (in either order) of the link of an apex of class `c`. -/
def LinkPair (c i j : Fin 4) : Prop :=
  LinkPat c (partner1 c) (partner2 c) i j ∨ LinkPat c (partner1 c) (partner2 c) j i

/-- Link pair types are `F₁`-allowed pairs. -/
lemma linkPair_allowed : ∀ c i j : Fin 4, LinkPair c i j → AllowedT F1 i j := by
  unfold LinkPair; decide

/-- The crossing star of `x` towards `N`. -/
def star (x : V) (N : Finset V) : Finset (Sym2 V) := N.image fun y => s(x, y)

/-- **Covering one crossing star** (produced).  Let `x ∉ N`, every `y ∈ N` adjacent to `x` and of
class `p x` or a partner class.  If every `y ∈ N` misses (non-adjacent, or edge in `B`) at most
`γ` vertices of each class `j` in `N` with `(p y, j)` a link pair type, and the margins and the parity hold, then there is a matching
`M ⊆ E(G) \ B` inside `N` (degree `≤ 1`) such that `star x N ∪ M` is `F₁`-decomposable. -/
theorem F1_apex_cover (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B : Finset (Sym2 V)) (x : V) (N : Finset V) (hxN : x ∉ N)
    (hstar : ∀ y ∈ N, G.Adj x y) (γ : ℕ)
    (hN : ∀ y ∈ N, p y = p x ∨ p y = partner1 (p x) ∨ p y = partner2 (p x))
    (hdense : ∀ y ∈ N, ∀ j : Fin 4, LinkPair (p x) (p y) j →
      (N.filter fun z => p z = j ∧ ¬ (G.Adj y z ∧ s(y, z) ∉ B)).card ≤ γ)
    (hac : 4 * γ + 1 ≤ (N.filter fun y => p y = p x).card)
    (ha1 : 6 * γ + 1 ≤ (N.filter fun y => p y = partner1 (p x)).card)
    (ha2 : 6 * γ + 1 ≤ (N.filter fun y => p y = partner2 (p x)).card)
    (hsum : (N.filter fun y => p y = p x).card + 8 * γ + 1 ≤
      (N.filter fun y => p y = partner1 (p x)).card +
        (N.filter fun y => p y = partner2 (p x)).card)
    (hpar : ((N.filter fun y => p y = p x).card +
      (N.filter fun y => p y = partner1 (p x)).card +
        (N.filter fun y => p y = partner2 (p x)).card) % 2 = 0) :
    ∃ M : Finset (Sym2 V), M ⊆ G.edgeFinset ∧ Disjoint M B ∧ (∀ e ∈ M, ∀ v ∈ e, v ∈ N) ∧
      (∀ v, (M.filter fun e => v ∈ e).card ≤ 1) ∧ HasDecomp p F1 (star x N ∪ M) := by
  classical
  obtain ⟨hc1, hc2, h12⟩ := partner_ne (p x)
  let ok : V → V → Prop := fun y z => G.Adj y z ∧ s(y, z) ∉ B
  have hsymm : ∀ y z, ok y z → ok z y := fun y z h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩
  obtain ⟨P, hP⟩ := link_pairing p (p x) (partner1 (p x)) (partner2 (p x)) hc1 hc2 h12 N ok
    hsymm γ hN hdense hac ha1 ha2 hsum hpar
  -- the pairing, in the graph-pairing format of `starTris_spec`
  have hpair : NashWilliams18.IsPairing G P := by
    refine ⟨fun q hq => (hP.ok q hq).1.1, fun q hq q' hq' hne => ?_⟩
    have hd := hP.disj q hq q' hq' hne
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · exact disjoint_left.mp hd (show q.1 ∈ ({q.1, q.2} : Finset V) by simp) (by simp [h])
    · exact disjoint_left.mp hd (show q.1 ∈ ({q.1, q.2} : Finset V) by simp) (by simp [h])
    · exact disjoint_left.mp hd (show q.2 ∈ ({q.1, q.2} : Finset V) by simp) (by simp [h])
    · exact disjoint_left.mp hd (show q.2 ∈ ({q.1, q.2} : Finset V) by simp) (by simp [h])
  have hverts : verts P = N := hP.cover
  have hz : ∀ w ∈ verts P, G.Adj x w := fun w hw => hstar w (hverts ▸ hw)
  obtain ⟨hcl, hdisj, hedges, -, -, -⟩ := starTris_spec G x P hpair hz
  let M : Finset (Sym2 V) := P.image fun q => s(q.1, q.2)
  have hxq1 : ∀ q ∈ P, x ≠ q.1 := fun q hq h => hxN (h ▸ hP.mem_left hq)
  have hxq2 : ∀ q ∈ P, x ≠ q.2 := fun q hq h => hxN (h ▸ hP.mem_right hq)
  refine ⟨M, ?_, ?_, ?_, ?_, ⟨starTris x P, ?_, hdisj, ?_⟩⟩
  · intro e he
    obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (hP.ok q hq).1.1
  · rw [disjoint_left]
    intro e he heB
    obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    exact (hP.ok q hq).1.2 heB
  · intro e he v hv
    obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hP.mem_left hq
    · exact hP.mem_right hq
  · intro v
    rw [card_le_one]
    intro e he e' he'
    obtain ⟨he, hve⟩ := mem_filter.mp he
    obtain ⟨he', hve'⟩ := mem_filter.mp he'
    obtain ⟨q, hq, rfl⟩ := mem_image.mp he
    obtain ⟨q', hq', rfl⟩ := mem_image.mp he'
    by_contra hne
    have hqq : q ≠ q' := fun h => hne (by rw [h])
    have hd := hP.disj q hq q' hq' hqq
    have h1 : v ∈ ({q.1, q.2} : Finset V) := by
      rcases Sym2.mem_iff.mp hve with rfl | rfl <;> simp
    have h2 : v ∈ ({q'.1, q'.2} : Finset V) := by
      rcases Sym2.mem_iff.mp hve' with rfl | rfl <;> simp
    exact disjoint_left.mp hd h1 h2
  · intro t ht
    obtain ⟨q, hq, rfl⟩ := mem_image.mp ht
    refine ⟨(hcl _ ht).card_eq, ?_⟩
    rw [triple_val_map p (hxq1 q hq) (hxq2 q hq) (hP.ne q hq)]
    exact linkPat_mem_F1 (p x) (p q.1) (p q.2) (hP.ok q hq).2
  · ext e
    rw [hedges e]
    simp only [star, M, mem_union, mem_image, hverts]
    constructor
    · rintro (⟨w, hw, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact Or.inl ⟨w, hw, rfl⟩
      · exact Or.inr ⟨q, hq, rfl⟩
    · rintro (⟨w, hw, rfl⟩ | ⟨q, hq, rfl⟩)
      · exact Or.inl ⟨w, hw, rfl⟩
      · exact Or.inr ⟨q, hq, rfl⟩

/-- The crossing load of `y`: the number of apexes whose crossing star contains `y`. -/
def crossLoad (X : Finset V) (N : V → Finset V) (y : V) : ℕ :=
  (X.filter fun x => y ∈ N x).card

/-- The `F₁` link margins and parity of an apex `x` with crossing star `N x` and defect `γ`. -/
def LinkMargins (p : V → Fin 4) (x : V) (N : Finset V) (γ : ℕ) : Prop :=
  4 * γ + 1 ≤ (N.filter fun y => p y = p x).card ∧
  6 * γ + 1 ≤ (N.filter fun y => p y = partner1 (p x)).card ∧
  6 * γ + 1 ≤ (N.filter fun y => p y = partner2 (p x)).card ∧
  (N.filter fun y => p y = p x).card + 8 * γ + 1 ≤
    (N.filter fun y => p y = partner1 (p x)).card +
      (N.filter fun y => p y = partner2 (p x)).card ∧
  ((N.filter fun y => p y = p x).card +
    (N.filter fun y => p y = partner1 (p x)).card +
      (N.filter fun y => p y = partner2 (p x)).card) % 2 = 0

/-- **Simultaneous crossing cover** (produced).  Let `X` be a set of apexes, `N x` (for `x ∈ X`)
crossing stars of `G`-neighbours of `x` outside `X`, of classes `F₁`-allowed for `x`.  Suppose
every `y ∈ N x` misses (w.r.t. `G` and `B₀`) at most `γ₀` vertices of each class in `N x` that
forms a link pair type with `p y`, every
vertex has crossing load `≤ γ₁`, and every apex satisfies the link margins and parity with
`γ = γ₀ + γ₁`.  Then there is `M ⊆ E(G) \ B₀`, all of whose edges avoid `X` and lie inside the
crossing stars, with degree `≤` crossing load at every vertex, such that
`⋃ₓ star x (N x) ∪ M` is `F₁`-decomposable. -/
theorem F1_crossing_cover (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (B₀ : Finset (Sym2 V)) (X : Finset V) (N : V → Finset V) (γ₀ γ₁ : ℕ)
    (hNX : ∀ x ∈ X, ∀ y ∈ N x, y ∉ X)
    (hstar : ∀ x ∈ X, ∀ y ∈ N x, G.Adj x y)
    (hcls : ∀ x ∈ X, ∀ y ∈ N x, p y = p x ∨ p y = partner1 (p x) ∨ p y = partner2 (p x))
    (hdense : ∀ x ∈ X, ∀ y ∈ N x, ∀ j : Fin 4, LinkPair (p x) (p y) j →
      ((N x).filter fun z => p z = j ∧ ¬ (G.Adj y z ∧ s(y, z) ∉ B₀)).card ≤ γ₀)
    (hload : ∀ y, crossLoad X N y ≤ γ₁)
    (hmarg : ∀ x ∈ X, LinkMargins p x (N x) (γ₀ + γ₁)) :
    ∃ M : Finset (Sym2 V), M ⊆ G.edgeFinset ∧ Disjoint M B₀ ∧
      (∀ e ∈ M, ∀ v ∈ e, v ∉ X ∧ ∃ x ∈ X, v ∈ N x) ∧
      (∀ v, (M.filter fun e => v ∈ e).card ≤ crossLoad X N v) ∧
      HasDecomp p F1 (X.biUnion (fun x => star x (N x)) ∪ M) := by
  classical
  -- induction over sub-families of apexes
  suffices H : ∀ Y ⊆ X, ∃ M : Finset (Sym2 V), M ⊆ G.edgeFinset ∧ Disjoint M B₀ ∧
      (∀ e ∈ M, ∀ v ∈ e, v ∉ X ∧ ∃ x ∈ Y, v ∈ N x) ∧
      (∀ v, (M.filter fun e => v ∈ e).card ≤ crossLoad Y N v) ∧
      HasDecomp p F1 (Y.biUnion (fun x => star x (N x)) ∪ M) by
    obtain ⟨M, h1, h2, h3, h4, h5⟩ := H X subset_rfl
    exact ⟨M, h1, h2, h3, h4, h5⟩
  intro Y
  induction Y using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨∅, empty_subset _, disjoint_empty_left _, by simp, by simp, ?_⟩
    simp only [biUnion_empty, union_empty]
    exact ⟨∅, by simp, by simp, by simp⟩
  | insert x Y hxY ih =>
    intro hsub
    have hxX : x ∈ X := hsub (mem_insert_self _ _)
    obtain ⟨M', hM'G, hM'B, hM'v, hM'deg, hM'dec⟩ := ih ((subset_insert _ _).trans hsub)
    have hloadY : ∀ v, crossLoad Y N v ≤ γ₁ := fun v =>
      (card_le_card (filter_subset_filter _ ((subset_insert _ _).trans hsub))).trans (hload v)
    -- apex `x` with forbidden set `B₀ ∪ M'`
    obtain ⟨hm1, hm2, hm3, hm4, hm5⟩ := hmarg x hxX
    have hdense' : ∀ y ∈ N x, ∀ j : Fin 4, LinkPair (p x) (p y) j → ((N x).filter fun z =>
        p z = j ∧ ¬ (G.Adj y z ∧ s(y, z) ∉ B₀ ∪ M')).card ≤ γ₀ + γ₁ := by
      intro y hy j hj
      have hsplit : ((N x).filter fun z => p z = j ∧ ¬ (G.Adj y z ∧ s(y, z) ∉ B₀ ∪ M')) ⊆
          ((N x).filter fun z => p z = j ∧ ¬ (G.Adj y z ∧ s(y, z) ∉ B₀)) ∪
            (N x).filter fun z => s(y, z) ∈ M' := by
        intro z hz
        obtain ⟨hzN, hzj, hbad⟩ := mem_filter.mp hz
        by_cases hzM : s(y, z) ∈ M'
        · exact mem_union_right _ (mem_filter.mpr ⟨hzN, hzM⟩)
        · refine mem_union_left _ (mem_filter.mpr ⟨hzN, hzj, fun h => hbad ⟨h.1, ?_⟩⟩)
          rw [mem_union, not_or]; exact ⟨h.2, hzM⟩
      have hM'y : ((N x).filter fun z => s(y, z) ∈ M').card ≤ γ₁ := by
        have hinj : ((N x).filter fun z => s(y, z) ∈ M').card ≤
            (M'.filter fun e => y ∈ e).card := by
          refine card_le_card_of_injOn (fun z => s(y, z)) ?_ ?_
          · intro z hz
            exact mem_filter.mpr ⟨(mem_filter.mp hz).2, Sym2.mem_mk_left _ _⟩
          · intro z _ z' _ h
            exact Sym2.congr_right.mp h
        exact hinj.trans ((hM'deg y).trans (hloadY y))
      exact (card_le_card hsplit).trans ((card_union_le _ _).trans (by
        have := hdense x hxX y hy j hj; omega))
    have hxN : x ∉ N x := fun h => hNX x hxX x h hxX
    obtain ⟨Mx, hMxG, hMxB, hMxv, hMxdeg, hMxdec⟩ := F1_apex_cover p G (B₀ ∪ M') x (N x) hxN
      (hstar x hxX) (γ₀ + γ₁) (hcls x hxX) hdense' hm1 hm2 hm3 hm4 hm5
    refine ⟨M' ∪ Mx, union_subset hM'G hMxG, ?_, ?_, ?_, ?_⟩
    · exact disjoint_union_left.mpr ⟨hM'B, (disjoint_union_right.mp hMxB).1⟩
    · intro e he v hv
      rcases mem_union.mp he with he | he
      · obtain ⟨h1, x', hx', h2⟩ := hM'v e he v hv
        exact ⟨h1, x', mem_insert_of_mem hx', h2⟩
      · have := hMxv e he v hv
        exact ⟨hNX x hxX v this, x, mem_insert_self _ _, this⟩
    · intro v
      have hxv : (Mx.filter fun e => v ∈ e).card ≤ if v ∈ N x then 1 else 0 := by
        split_ifs with h
        · exact hMxdeg v
        · rw [Nat.le_zero, card_eq_zero, filter_eq_empty_iff]
          intro e he hve
          exact h (hMxv e he v hve)
      have hcl : crossLoad (insert x Y) N v =
          crossLoad Y N v + if v ∈ N x then 1 else 0 := by
        unfold crossLoad
        rw [filter_insert]
        split_ifs with h
        · rw [card_insert_of_notMem (fun hx => hxY (mem_filter.mp hx).1)]
        · rfl
      rw [hcl, filter_union]
      exact (card_union_le _ _).trans (Nat.add_le_add (hM'deg v) hxv)
    · -- assemble the two decompositions
      have hdisj : Disjoint (Y.biUnion (fun x => star x (N x)) ∪ M') (star x (N x) ∪ Mx) := by
        rw [disjoint_left]
        intro e he he'
        rcases mem_union.mp he' with hs | hm
        · -- `e = s(x, y)` with `y ∈ N x`
          obtain ⟨y, hy, rfl⟩ := mem_image.mp hs
          rcases mem_union.mp he with hY | hM
          · obtain ⟨x', hx', hs'⟩ := mem_biUnion.mp hY
            obtain ⟨y', hy', heq⟩ := mem_image.mp hs'
            have hxx' : x ≠ x' := fun h => hxY (h ▸ hx')
            rcases Sym2.eq_iff.mp heq with ⟨h1, -⟩ | ⟨h1, -⟩
            · exact hxx' h1.symm
            · exact hNX x hxX y hy (h1 ▸ hsub (mem_insert_of_mem hx'))
          · exact (hM'v _ hM x (Sym2.mem_mk_left _ _)).1 hxX
        · rcases mem_union.mp he with hY | hM
          · obtain ⟨x', hx', hs'⟩ := mem_biUnion.mp hY
            obtain ⟨y', -, rfl⟩ := mem_image.mp hs'
            have := hMxv _ hm x' (Sym2.mem_mk_left _ _)
            exact hNX x hxX x' this (hsub (mem_insert_of_mem hx'))
          · exact disjoint_left.mp hMxB hm (mem_union_right _ hM)
      have hfin := hM'dec.union hMxdec hdisj
      have heq : Y.biUnion (fun x => star x (N x)) ∪ M' ∪ (star x (N x) ∪ Mx) =
          (insert x Y).biUnion (fun x => star x (N x)) ∪ (M' ∪ Mx) := by
        rw [biUnion_insert]
        ext e; simp only [mem_union]; tauto
      rwa [heq] at hfin

end NashWilliams18.CrossingCover
