/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.CrossingCoverF1
public import RequestProject.NW18.Case126.SpreadMatchingGen

@[expose] public section

/-!
# Theorem 14.7 for `F₁`, vortex route: SPREAD root cover-down at many roots (produced)

This is the terminal pairing step of an `F₁` vortex level in the regime that
`CrossingCover.crossing_cover_regime` proved unreachable for the worst-case crossing cover: the
number of roots `k` may be much larger than the child set `U`.

* `inv_of_perfectPairing` (new): a perfect pairing (`LinkPairing.IsPerfectPairing`) as a
  fixed-point-free involution.
* `F1_single_matching` (new): ONE typed `F₁` link matching of a target `T` avoiding a consumed graph
  of trace `≤ D` inside `T`, from `LinkPairing.link_pairing` (Hall); explicit density defect `γ₀`,
  margins with `γ₀ + D`, parity.
* `F1_root_cover_down_of_matchings` (adapted from the `F0` lemma `root_cover_down_of_matchings`
  of the L3 F0 project, with the `F₁` link types instead of the `F0` labels): pairwise
  edge-disjoint `F₁` link matchings at distinct roots close all root stars by actual `F₁`
  triangles.
* `F1_spread_root_cover_down` (new assembly for `F₁`, using the generic spread potential
  `SpreadGen.spread_matching_of_family` adapted from the F0 project): all roots at once, with the
  SECOND ORDER budget `(e-1) ω L / K + log ∑ |T i| ≤ B` instead of `load ≤ degree into the target`.

**Inputs and where they come from.**  `T i` is the crossing star of the root `x i` into `U` that
is left after the approximate packing (leftover + crossing reserve).  `R` is the internal reserve
inside `U`; taking `R` without edges inside the next set `U'` gives the avoidance of `U'`.  The
density defect `γ₀` counts, for `v ∈ T i`, the vertices of a link-pair class in `T i` that are not
`R`-neighbours of `v` (it contains `|T i ∩ U'|` for `v ∈ U'`, and the non-edges of the host inside
`T i`).  `ω` bounds the overlaps `|T i ∩ T j|` and `L` the number of targets through a vertex.
These are statistics of the joint random reserve and of the nibble leftover; they are NOT produced
here (see `VortexLevelF1.lean`, `F1LevelSupply`).
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption LinkPairing CrossingCover SpreadGen
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [DecidableEq V]

/-- A perfect pairing, read as a fixed-point-free involution. -/
theorem inv_of_perfectPairing {N : Finset V} {P : Finset (V × V)} {r : V → V → Prop}
    (h : IsPerfectPairing N P r) (hsymm : ∀ y z, r y z → r z y) :
    ∃ f : V → V, ∀ v ∈ N, f v ∈ N ∧ f v ≠ v ∧ f (f v) = v ∧ r v (f v) := by
  classical
  have hex : ∀ v ∈ N, ∃ q ∈ P, q.1 = v ∨ q.2 = v := by
    intro v hv
    rw [← h.cover] at hv
    obtain ⟨q, hq, hvq⟩ := mem_biUnion.mp hv
    simp only [mem_insert, mem_singleton] at hvq
    exact ⟨q, hq, by rcases hvq with h | h <;> [left; right] <;> exact h.symm⟩
  have huniq : ∀ q ∈ P, ∀ q' ∈ P, ∀ v, (q.1 = v ∨ q.2 = v) → (q'.1 = v ∨ q'.2 = v) →
      q = q' := by
    intro q hq q' hq' v hv hv'
    by_contra hne
    have hd := h.disj q hq q' hq' hne
    have h1 : v ∈ ({q.1, q.2} : Finset V) := by rcases hv with h | h <;> simp [h]
    have h2 : v ∈ ({q'.1, q'.2} : Finset V) := by rcases hv' with h | h <;> simp [h]
    exact disjoint_left.mp hd h1 h2
  let f : V → V := fun v =>
    if hq : ∃ q ∈ P, q.1 = v ∨ q.2 = v then
      (if (Classical.choose hq).1 = v then (Classical.choose hq).2 else (Classical.choose hq).1)
    else v
  have hf : ∀ q ∈ P, f q.1 = q.2 ∧ f q.2 = q.1 := by
    intro q hq
    have hne := h.ne q hq
    have e1 : ∃ q' ∈ P, q'.1 = q.1 ∨ q'.2 = q.1 := ⟨q, hq, Or.inl rfl⟩
    have e2 : ∃ q' ∈ P, q'.1 = q.2 ∨ q'.2 = q.2 := ⟨q, hq, Or.inr rfl⟩
    have c1 := Classical.choose_spec e1
    have c2 := Classical.choose_spec e2
    have q1 : Classical.choose e1 = q := huniq _ c1.1 q hq q.1 c1.2 (Or.inl rfl)
    have q2 : Classical.choose e2 = q := huniq _ c2.1 q hq q.2 c2.2 (Or.inr rfl)
    constructor
    · simp only [f, dif_pos e1, q1, ↓reduceIte]
    · simp only [f, dif_pos e2, q2]
      rw [if_neg hne]
  refine ⟨f, fun v hv => ?_⟩
  obtain ⟨q, hq, hvq⟩ := hex v hv
  obtain ⟨hf1, hf2⟩ := hf q hq
  have hne := h.ne q hq
  rcases hvq with rfl | rfl
  · exact ⟨hf1 ▸ h.mem_right hq, hf1 ▸ hne.symm, by rw [hf1, hf2], hf1 ▸ h.ok q hq⟩
  · exact ⟨hf2 ▸ h.mem_left hq, hf2 ▸ hne, by rw [hf2, hf1], hf2 ▸ hsymm _ _ (h.ok q hq)⟩

/-- The `F₁` link pair predicate of a root of class `c`. -/
def okF1 (p : V → Fin 4) (c : Fin 4) : V → V → Prop := fun v w => LinkPair c (p v) (p w)

/-- The `F₁` link margins and parity of a target `T` for a root class `c`, with defect `γ`. -/
def TargetMargins (p : V → Fin 4) (c : Fin 4) (T : Finset V) (γ : ℕ) : Prop :=
  4 * γ + 1 ≤ (T.filter fun y => p y = c).card ∧
  6 * γ + 1 ≤ (T.filter fun y => p y = partner1 c).card ∧
  6 * γ + 1 ≤ (T.filter fun y => p y = partner2 c).card ∧
  (T.filter fun y => p y = c).card + 8 * γ + 1 ≤
    (T.filter fun y => p y = partner1 c).card + (T.filter fun y => p y = partner2 c).card ∧
  ((T.filter fun y => p y = c).card + (T.filter fun y => p y = partner1 c).card +
    (T.filter fun y => p y = partner2 c).card) % 2 = 0

/-- **One typed `F₁` link matching avoiding a consumed graph** (produced, new).  Let every vertex
of `T` have class `c` or a partner class of `c`.  If every `v ∈ T` misses (not an `R`-neighbour, or
`v` itself) at most `γ₀` vertices of each class of `T` forming an `F₁` link pair type with `p v`,
and the consumed graph `G` has trace `≤ D` inside `T` at every vertex of `T`, and the margins and
parity hold with `γ₀ + D`, then `T` has a perfect `F₁` link matching by edges of `R \ G`. -/
theorem F1_single_matching (p : V → Fin 4) (c : Fin 4) (T : Finset V) (R G : Finset (Sym2 V))
    (γ₀ D : ℕ)
    (hcls : ∀ y ∈ T, p y = c ∨ p y = partner1 c ∨ p y = partner2 c)
    (hdense : ∀ y ∈ T, ∀ j : Fin 4, LinkPair c (p y) j →
      (T.filter fun z => p z = j ∧ ¬ (z ≠ y ∧ s(y, z) ∈ R)).card ≤ γ₀)
    (hG : ∀ v ∈ T, (T.filter (fun w => s(v, w) ∈ G)).card ≤ D)
    (hmarg : TargetMargins p c T (γ₀ + D)) :
    ∃ h : V → V, IsOkMatching (okF1 p c) T (R \ G) h := by
  classical
  obtain ⟨hc1, hc2, h12⟩ := partner_ne c
  obtain ⟨m1, m2, m3, m4, m5⟩ := hmarg
  let ok : V → V → Prop := fun y z => z ≠ y ∧ s(y, z) ∈ R \ G
  have hsymm : ∀ y z, ok y z → ok z y := fun y z hyz =>
    ⟨hyz.1.symm, by rw [Sym2.eq_swap]; exact hyz.2⟩
  have hdense' : ∀ y ∈ T, ∀ j : Fin 4,
      (LinkPat c (partner1 c) (partner2 c) (p y) j ∨ LinkPat c (partner1 c) (partner2 c) j (p y)) →
      (T.filter fun z => p z = j ∧ ¬ ok y z).card ≤ γ₀ + D := by
    intro y hy j hj
    have hsub : (T.filter fun z => p z = j ∧ ¬ ok y z) ⊆
        (T.filter fun z => p z = j ∧ ¬ (z ≠ y ∧ s(y, z) ∈ R)) ∪
          T.filter (fun w => s(y, w) ∈ G) := by
      intro z hz
      obtain ⟨hzT, hzj, hbad⟩ := mem_filter.mp hz
      by_cases hzG : s(y, z) ∈ G
      · exact mem_union_right _ (mem_filter.mpr ⟨hzT, hzG⟩)
      · refine mem_union_left _ (mem_filter.mpr ⟨hzT, hzj, fun hok => hbad ⟨hok.1, ?_⟩⟩)
        exact mem_sdiff.mpr ⟨hok.2, hzG⟩
    exact (card_le_card hsub).trans ((card_union_le _ _).trans
      (add_le_add (hdense y hy j hj) (hG y hy)))
  obtain ⟨P, hP⟩ := link_pairing p c (partner1 c) (partner2 c) hc1 hc2 h12 T ok hsymm (γ₀ + D)
    hcls hdense' m1 m2 m3 m4 m5
  have hsymm' : ∀ y z, (ok y z ∧ LinkPair c (p y) (p z)) → (ok z y ∧ LinkPair c (p z) (p y)) :=
    fun y z hyz => ⟨hsymm y z hyz.1, by unfold LinkPair at *; tauto⟩
  have hP' : IsPerfectPairing T P (fun y z => ok y z ∧ LinkPair c (p y) (p z)) :=
    hP.mono (fun y z hyz => ⟨hyz.1, Or.inl hyz.2⟩)
  obtain ⟨f, hf⟩ := inv_of_perfectPairing hP' hsymm'
  refine ⟨f, fun v hv => ?_⟩
  obtain ⟨h1, h2, h3, ⟨-, h4⟩, h5⟩ := hf v hv
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The star of the roots: the edges `x i — v`, `v ∈ T i`. -/
def rootStar (k : ℕ) (x : ℕ → V) (T : ℕ → Finset V) : Finset (Sym2 V) :=
  (range k).biUnion (fun i => (T i).image (fun v => s(x i, v)))

theorem deg_biUnion_le (k : ℕ) (E : ℕ → Finset (Sym2 V)) (v : V) :
    deg ((range k).biUnion E) v ≤ ∑ i ∈ range k, deg (E i) v := by
  unfold deg
  rw [Finset.filter_biUnion]
  exact Finset.card_biUnion_le

/-- **`F₁` root cover-down from given matchings** (adapted from the F0 project's
`root_cover_down_of_matchings`).  Pairwise edge-disjoint `F₁` link matchings at distinct roots
(outside all targets) close all root stars by actual `F₁` triangles `{x i, v, f i v}`.  The
consumed graph `M` is the union of the matchings; its degree at `v` is at most the number of
targets through `v`. -/
theorem F1_root_cover_down_of_matchings (p : V → Fin 4) (R : Finset (Sym2 V)) (k : ℕ)
    (x : ℕ → V) (T : ℕ → Finset V) (f : ℕ → V → V)
    (hx : ∀ i < k, ∀ j < k, x i = x j → i = j)
    (hxT : ∀ i < k, ∀ j < k, x i ∉ T j)
    (hf : ∀ i < k, IsOkMatching (okF1 p (p (x i))) (T i) R (f i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j → Disjoint (matchEdges (T i) (f i)) (matchEdges (T j) (f j))) :
    ∃ M : Finset (Sym2 V), M ⊆ R ∧
      (∀ v, deg M v ≤ visits T k v) ∧
      Disjoint (rootStar k x T) M ∧ HasDecomp p F1 (rootStar k x T ∪ M) := by
  classical
  set M := (range k).biUnion (fun i => matchEdges (T i) (f i)) with hM
  have hMR : M ⊆ R := by
    intro e he
    obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
    exact matchEdges_subset (hf i (Finset.mem_range.mp hi)) he
  have hMroot : ∀ e ∈ M, ∀ i < k, x i ∉ e := by
    intro e he i hi hxe
    obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
    exact hxT i hi j (Finset.mem_range.mp hj)
      (mem_matchEdges (hf j (Finset.mem_range.mp hj)) he hxe).1
  have hdegM : ∀ v, deg M v ≤ visits T k v := by
    intro v
    refine (deg_biUnion_le k _ v).trans ?_
    unfold visits
    rw [Finset.card_filter]
    apply Finset.sum_le_sum
    intro i hi
    exact deg_matchEdges_le (hf i (Finset.mem_range.mp hi)) v
  have hstarM : Disjoint (rootStar k x T) M := by
    rw [Finset.disjoint_left]
    intro e he heM
    simp only [rootStar, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at he
    obtain ⟨i, hi, v, -, rfl⟩ := he
    exact hMroot _ heM i hi (Sym2.mem_mk_left _ _)
  let tri : ℕ → V → Finset V := fun i v => {x i, v, f i v}
  have hdist : ∀ i < k, ∀ v ∈ T i, x i ≠ v ∧ x i ≠ f i v ∧ v ≠ f i v := by
    intro i hi v hv
    obtain ⟨h1, h2, -⟩ := hf i hi v hv
    refine ⟨fun h => hxT i hi i hi (h ▸ hv), fun h => hxT i hi i hi (h ▸ h1), fun h => h2 h.symm⟩
  have htriE : ∀ i < k, ∀ v ∈ T i,
      triEdges (tri i v) = {s(x i, v), s(x i, f i v), s(v, f i v)} := by
    intro i hi v hv
    obtain ⟨a, b, c⟩ := hdist i hi v hv
    exact PartitionedTriangleAbsorption.triEdges_three a b c
  have htri_swap : ∀ i < k, ∀ v ∈ T i, tri i (f i v) = tri i v := by
    intro i hi v hv
    obtain ⟨-, -, h3, -⟩ := hf i hi v hv
    simp only [tri, h3]
    ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hrigid : ∀ i < k, ∀ v ∈ T i, ∀ j < k, ∀ w ∈ T j, ∀ e,
      e ∈ triEdges (tri i v) → e ∈ triEdges (tri j w) → tri i v = tri j w := by
    intro i hi v hv j hj w hw e he he'
    rw [htriE i hi v hv] at he
    rw [htriE j hj w hw] at he'
    have hfv := (hf i hi v hv).1
    have hfw := (hf j hj w hw).1
    have hMi : s(v, f i v) ∈ matchEdges (T i) (f i) := Finset.mem_image_of_mem _ hv
    have hMj : s(w, f j w) ∈ matchEdges (T j) (f j) := Finset.mem_image_of_mem _ hw
    have hMv : s(v, f i v) ∈ M := Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi, hMi⟩
    have hMw : s(w, f j w) ∈ M := Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, hMj⟩
    have hroot : ∀ a ∈ T i, ∀ b ∈ T j, s(x i, a) = s(x j, b) → i = j ∧ a = b := by
      intro a ha b hb hab
      rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, -⟩
      · exact ⟨hx i hi j hj h1, h2⟩
      · exact absurd (h1 ▸ hb) (hxT i hi j hj)
    have hpair : ∀ a, (a = v ∨ a = f i v) → (a = w ∨ a = f i w) → i = j →
        tri i v = tri j w := by
      intro a ha ha' hij
      subst hij
      have hT : ∀ u ∈ T i, (a = u ∨ a = f i u) → tri i a = tri i u := by
        intro u hu hau
        rcases hau with hau | hau
        · rw [hau]
        · rw [hau, htri_swap i hi u hu]
      rw [← hT v hv ha, hT w hw ha']
    simp only [Finset.mem_insert, Finset.mem_singleton] at he he'
    rcases he with rfl | rfl | rfl <;> rcases he' with h | h | h
    · obtain ⟨hij, hab⟩ := hroot _ hv _ hw h; exact hpair v (Or.inl rfl) (Or.inl hab) hij
    · obtain ⟨hij, hab⟩ := hroot _ hv _ hfw h
      subst hij; exact hpair v (Or.inl rfl) (Or.inr hab) rfl
    · exact absurd (h ▸ hMw) (fun hm => hMroot _ hm i hi (Sym2.mem_mk_left _ _))
    · obtain ⟨hij, hab⟩ := hroot _ hfv _ hw h
      subst hij; exact hpair (f i v) (Or.inr rfl) (Or.inl hab) rfl
    · obtain ⟨hij, hab⟩ := hroot _ hfv _ hfw h
      subst hij; exact hpair (f i v) (Or.inr rfl) (Or.inr hab) rfl
    · exact absurd (h ▸ hMw) (fun hm => hMroot _ hm i hi (Sym2.mem_mk_left _ _))
    · exact absurd (h.symm ▸ hMv) (fun hm => hMroot _ hm j hj (Sym2.mem_mk_left _ _))
    · exact absurd (h.symm ▸ hMv) (fun hm => hMroot _ hm j hj (Sym2.mem_mk_left _ _))
    · by_cases hij : i = j
      · subst hij
        rcases Sym2.eq_iff.mp h with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact hpair v (Or.inl rfl) (Or.inl h1) rfl
        · exact hpair v (Or.inl rfl) (Or.inr h1) rfl
      · rw [← h] at hMj
        exact absurd hMj (Finset.disjoint_left.mp (hdisj i hi j hj hij) hMi)
  refine ⟨M, hMR, hdegM, hstarM, (range k).biUnion (fun i => (T i).image (tri i)), ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨i, hi, hs⟩ := Finset.mem_biUnion.mp hs
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hs
    have hi' := Finset.mem_range.mp hi
    obtain ⟨a, b, c⟩ := hdist i hi' v hv
    refine ⟨?_, ?_⟩
    · simp only [tri]
      rw [Finset.card_insert_of_notMem (by simp [a, b]),
        Finset.card_insert_of_notMem (by simp [c]), Finset.card_singleton]
    · simp only [tri]
      rw [triple_val_map p a b c]
      rcases (hf i hi' v hv).2.2.2.2 with h | h
      · exact linkPat_mem_F1 _ _ _ h
      · have := linkPat_mem_F1 _ _ _ h
        rwa [show ({p v, p (f i v)} : Multiset (Fin 4)) = {p (f i v), p v} from
          Multiset.pair_comm _ _]
  · intro s hs s' hs' hss
    simp only [Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion, Finset.coe_image,
      Set.mem_image, Set.mem_Iio, Finset.mem_coe] at hs hs'
    obtain ⟨i, hi, v, hv, rfl⟩ := hs
    obtain ⟨j, hj, w, hw, rfl⟩ := hs'
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    exact hss (hrigid i hi v hv j hj w hw e he he')
  · ext e
    simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_image, Finset.mem_union]
    constructor
    · rintro ⟨s, ⟨i, hi, v, hv, rfl⟩, he⟩
      rw [htriE i hi v hv] at he
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with rfl | rfl | rfl
      · exact Or.inl (by
          simp only [rootStar, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
          exact ⟨i, hi, v, hv, rfl⟩)
      · exact Or.inl (by
          simp only [rootStar, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
          exact ⟨i, hi, f i v, (hf i hi v hv).1, rfl⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_range.mpr hi,
          Finset.mem_image_of_mem _ hv⟩)
    · rintro (he | he)
      · simp only [rootStar, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image] at he
        obtain ⟨i, hi, v, hv, rfl⟩ := he
        refine ⟨tri i v, ⟨i, hi, v, hv, rfl⟩, ?_⟩
        rw [htriE i hi v hv]; simp
      · obtain ⟨i, hi, he⟩ := Finset.mem_biUnion.mp he
        simp only [matchEdges, Finset.mem_image] at he
        obtain ⟨v, hv, rfl⟩ := he
        have hi' := Finset.mem_range.mp hi
        refine ⟨tri i v, ⟨i, hi', v, hv, rfl⟩, ?_⟩
        rw [htriE i hi' v hv]; simp

/-- **Spread `F₁` root cover-down** (produced; new `F₁` assembly of the spread potential adapted
from the F0 project).  Distinct roots `x i` outside all targets `T i`; every vertex of `T i` has
class `p (x i)` or a partner class; every `v ∈ T i` misses at most `γ₀` vertices of `T i` of each
class forming an `F₁` link pair type with `p v` (w.r.t. the internal reserve `R`); every target has
the `F₁` margins and parity with defect `γ₀ + B + K`; distinct targets overlap in `≤ ω` vertices,
every vertex lies in `≤ L` targets, and `(e-1) ω L / K + log ∑ |T i| ≤ B` with `K > 0`.

Then there is `M ⊆ R` with `deg M v ≤ L` such that the root stars together with `M` have an actual
`F₁`-decomposition.  NOTE: the load `L` is never compared with the target sizes; this is what lets
the number of roots exceed `|U|` (contrast with `crossing_cover_regime`). -/
theorem F1_spread_root_cover_down (p : V → Fin 4) (R : Finset (Sym2 V)) (k : ℕ)
    (x : ℕ → V) (T : ℕ → Finset V) (γ₀ K B ω L : ℕ) (hK : 0 < K)
    (hx : ∀ i < k, ∀ j < k, x i = x j → i = j)
    (hxT : ∀ i < k, ∀ j < k, x i ∉ T j)
    (hcls : ∀ i < k, ∀ y ∈ T i,
      p y = p (x i) ∨ p y = partner1 (p (x i)) ∨ p y = partner2 (p (x i)))
    (hdense : ∀ i < k, ∀ y ∈ T i, ∀ j : Fin 4, LinkPair (p (x i)) (p y) j →
      ((T i).filter fun z => p z = j ∧ ¬ (z ≠ y ∧ s(y, z) ∈ R)).card ≤ γ₀)
    (hmarg : ∀ i < k, TargetMargins p (p (x i)) (T i) (γ₀ + (B + K)))
    (hover : ∀ i < k, ∀ j < k, i ≠ j → ((T i) ∩ (T j)).card ≤ ω)
    (hload : ∀ v, visits T k v ≤ L)
    (hB : (Real.exp 1 - 1) * ω * L / K + Real.log (∑ i ∈ range k, ((T i).card : ℝ)) ≤ B) :
    ∃ M : Finset (Sym2 V), M ⊆ R ∧ (∀ v, deg M v ≤ L) ∧
      Disjoint (rootStar k x T) M ∧ HasDecomp p F1 (rootStar k x T ∪ M) := by
  obtain ⟨f, hf, hdisj⟩ := spread_matching_of_family (fun i => okF1 p (p (x i))) R k T K B ω L hK
    (fun t ht F hF => perRootFamily_of_single _ (T t) R F K B hF (fun G hG =>
      F1_single_matching p (p (x t)) (T t) R G γ₀ (B + K) (hcls t ht) (hdense t ht) hG
        (hmarg t ht)))
    hover hload hB
  obtain ⟨M, h1, h2, h3, h4⟩ := F1_root_cover_down_of_matchings p R k x T f hx hxT hf hdisj
  exact ⟨M, h1, fun v => (h2 v).trans (hload v), h3, h4⟩

end NashWilliams18.SpreadF1
