/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.SpreadPairingF1
import RequestProject.NW18.Case124.OneScale.SpreadMatchingDirac
import RequestProject.NW18.Base

/-!
# Spread `K₃` root cover-down (ordinary triangles)

The ordinary-triangle analogue of `SpreadF1.F1_spread_root_cover_down`: each root `x i` has a
target `T i` (its remaining cross neighbourhood), and the root star `x i — T i` is closed by the
triangles `{x i, v, f i v}` for a perfect matching `f i` of `T i` by edges of an internal reserve
`R`.  The matchings of different roots are chosen pairwise edge-disjoint by the generic spread
potential argument `SpreadGen.spread_matching_of_family`, and each single matching comes from
Dirac's theorem (`SimpleGraph.exists_involution_adj`).

* `K3_single_matching`: an even target in which every vertex misses at most `γ₀` `R`-neighbours
  and `D` consumed edges, with `γ₀ + D + |T|/2 ≤ |T|`, has a perfect matching by edges of `R \ G`.
* `K3_root_cover_down_of_matchings`: given pairwise edge-disjoint matchings, the root stars plus
  the matching edges are `K₃`-decomposable; the consumed degree at `v` is at most the number of
  targets through `v`.
* `K3_spread_root_cover_down`: the combination.
-/

namespace NashWilliams18.SpreadK3

open Finset PartitionedTriangleAbsorption SpreadGen SpreadF1

variable {V : Type} [DecidableEq V]

/-- **One `K₃` root matching by Dirac's theorem.** -/
theorem K3_single_matching (T : Finset V) (R G : Finset (Sym2 V)) (γ₀ D : ℕ)
    (hEven : Even T.card)
    (hdense : ∀ y ∈ T, (T.filter fun z => ¬ (z ≠ y ∧ s(y, z) ∈ R)).card ≤ γ₀)
    (hG : ∀ v ∈ T, (T.filter (fun w => s(v, w) ∈ G)).card ≤ D)
    (hmarg : γ₀ + D + T.card / 2 ≤ T.card) :
    ∃ h : V → V, IsOkMatching (fun _ _ => True) T (R \ G) h := by
  classical
  let H : SimpleGraph V := SimpleGraph.fromRel (fun y z => s(y, z) ∈ R \ G)
  have hadj : ∀ y z, z ≠ y → s(y, z) ∈ R \ G → H.Adj y z := by
    intro y z hzy hyz
    exact ⟨fun h => hzy h.symm, Or.inl hyz⟩
  have hdeg : ∀ v ∈ T, T.card / 2 ≤ (T.filter fun z => H.Adj v z).card := by
    intro v hv
    have hsub : T.filter (fun z => ¬ H.Adj v z) ⊆
        (T.filter fun z => ¬ (z ≠ v ∧ s(v, z) ∈ R)) ∪ T.filter (fun w => s(v, w) ∈ G) := by
      intro z hz
      obtain ⟨hzT, hnadj⟩ := mem_filter.mp hz
      by_cases hzG : s(v, z) ∈ G
      · exact mem_union_right _ (mem_filter.mpr ⟨hzT, hzG⟩)
      · refine mem_union_left _ (mem_filter.mpr ⟨hzT, fun hok => hnadj ?_⟩)
        exact hadj v z hok.1 (mem_sdiff.mpr ⟨hok.2, hzG⟩)
    have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
      (add_le_add (hdense v hv) (hG v hv)))
    have h2 := card_filter_add_card_filter_not (s := T) (fun z => H.Adj v z)
    omega
  obtain ⟨f, hfT, hfinv, hfne, hfadj⟩ := SimpleGraph.exists_involution_adj hEven hdeg
  refine ⟨f, fun v hv => ⟨hfT v hv, hfne v hv, hfinv v hv, ?_, trivial⟩⟩
  obtain ⟨-, h | h⟩ := hfadj v hv
  · exact h
  · rwa [Sym2.eq_swap]

/-- **`K₃` root cover-down from given matchings.** -/
theorem K3_root_cover_down_of_matchings (R : Finset (Sym2 V)) (k : ℕ)
    (x : ℕ → V) (T : ℕ → Finset V) (f : ℕ → V → V)
    (hx : ∀ i < k, ∀ j < k, x i = x j → i = j)
    (hxT : ∀ i < k, ∀ j < k, x i ∉ T j)
    (hf : ∀ i < k, IsOkMatching (fun _ _ => True) (T i) R (f i))
    (hdisj : ∀ i < k, ∀ j < k, i ≠ j →
      Disjoint (matchEdges (T i) (f i)) (matchEdges (T j) (f j))) :
    ∃ M : Finset (Sym2 V), M ⊆ R ∧
      (∀ v, deg M v ≤ visits T k v) ∧
      Disjoint (rootStar k x T) M ∧ HasDecomp onePart K3fam (rootStar k x T ∪ M) := by
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
    have hcard : (tri i v).card = 3 := by
      simp only [tri]
      rw [Finset.card_insert_of_notMem (by simp [a, b]),
        Finset.card_insert_of_notMem (by simp [c]), Finset.card_singleton]
    refine ⟨hcard, ?_⟩
    rw [map_onePart hcard]
    simp [K3fam]
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

/-- **Spread `K₃` root cover-down.**  Distinct roots `x i` outside all targets; every target is
even, every vertex of `T i` misses at most `γ₀` `R`-neighbours inside `T i`, the Dirac margin
`γ₀ + (B + K) + |T i|/2 ≤ |T i|` holds, distinct targets overlap in `≤ ω` vertices, every vertex
lies in `≤ L` targets and `(e-1) ω L / K + log ∑ |T i| ≤ B` with `K > 0`.  Then some `M ⊆ R`
with `deg M v ≤ L` makes the root stars plus `M` triangle-decomposable. -/
theorem K3_spread_root_cover_down (R : Finset (Sym2 V)) (k : ℕ)
    (x : ℕ → V) (T : ℕ → Finset V) (γ₀ K B ω L : ℕ) (hK : 0 < K)
    (hx : ∀ i < k, ∀ j < k, x i = x j → i = j)
    (hxT : ∀ i < k, ∀ j < k, x i ∉ T j)
    (heven : ∀ i < k, Even (T i).card)
    (hdense : ∀ i < k, ∀ y ∈ T i, ((T i).filter fun z => ¬ (z ≠ y ∧ s(y, z) ∈ R)).card ≤ γ₀)
    (hmarg : ∀ i < k, γ₀ + (B + K) + (T i).card / 2 ≤ (T i).card)
    (hover : ∀ i < k, ∀ j < k, i ≠ j → ((T i) ∩ (T j)).card ≤ ω)
    (hload : ∀ v, visits T k v ≤ L)
    (hB : (Real.exp 1 - 1) * ω * L / K + Real.log (∑ i ∈ range k, ((T i).card : ℝ)) ≤ B) :
    ∃ M : Finset (Sym2 V), M ⊆ R ∧ (∀ v, deg M v ≤ L) ∧
      Disjoint (rootStar k x T) M ∧ HasDecomp onePart K3fam (rootStar k x T ∪ M) := by
  obtain ⟨f, hf, hdisj⟩ := spread_matching_of_family (fun _ _ _ => True) R k T K B ω L hK
    (fun t ht F hF => perRootFamily_of_single _ (T t) R F K B hF (fun G hG =>
      K3_single_matching (T t) R G γ₀ (B + K) (heven t ht) (hdense t ht) hG (hmarg t ht)))
    hover hload hB
  obtain ⟨M, h1, h2, h3, h4⟩ := K3_root_cover_down_of_matchings R k x T f hx hxT hf hdisj
  exact ⟨M, h1, fun v => (h2 v).trans (hload v), h3, h4⟩

end NashWilliams18.SpreadK3
