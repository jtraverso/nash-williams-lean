/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.LevelRepairF1
import RequestProject.NW18.Case126.NearQuarterF1

/-!
# The protected `F₁` level, part 2: physical counts of the cross neighbourhoods

For the SAME sampled reserve `R` and an arbitrary perturbation `E` of maximum degree controlled
by the caller (in the level: the boundary charge correction together with the cross leftover of
the nibble), the cross graph is `Q = R ∪ E` and the cross neighbourhood of a root `r` is
`tgt U Q r`.  This file proves, from the level hypotheses and the reserve statistics only:

* `tgt_cls_lower` / `tgt_cls_upper`: class counts of `tgt U Q r`, centred at `ρ |U_c|`;
* `tgt_defect`: the link defect w.r.t. the internal reserve `E(H[U]) \ E(H[U'])`, from the
  physical bad-set query (an UPPER bound, no unfiltered centring is used);
* `tgt_overlap`: pairwise overlaps of two cross neighbourhoods;
* `visits_le`: the visit load of a child vertex;
* `apex_count_lower`: the typed apex candidates of an outer pair, for `Q ⊇ R`.
-/

namespace NashWilliams18.SpreadF1

open Finset PartitionedTriangleAbsorption LinkPairing CrossingCover SpreadGen
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- Neighbours of `r` in `U` through `E` are at most the `E`-degree of `r`. -/
theorem nbrU_le_deg (U : Finset V) (E : Finset (Sym2 V)) (r : V) :
    ((U.filter fun z => s(r, z) ∈ E).card : ℝ) ≤ (E.filter fun e => r ∈ e).card := by
  exact_mod_cast nbr_card_le_deg U E r

omit [Fintype V] in
theorem tgt_union_sub (U : Finset V) (R E : Finset (Sym2 V)) (r : V) (P : V → Prop)
    [DecidablePred P] :
    (tgt U (R ∪ E) r).filter P ⊆
      (U.filter fun z => P z ∧ s(r, z) ∈ R) ∪ (U.filter fun z => s(r, z) ∈ E) := by
  intro z hz
  simp only [tgt, mem_filter, mem_union] at hz ⊢
  obtain ⟨⟨hzU, hRE⟩, hP⟩ := hz
  rcases hRE with h | h
  · exact Or.inl ⟨hzU, hP, h⟩
  · exact Or.inr ⟨hzU, h⟩

section Counts

variable {p : V → Fin 4} {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
  {W U U' : Finset V} {β κ ξ ζ : ℝ}

/-- Missing neighbours of a vertex of `W` in a class of `U`, in the current graph. -/
theorem miss_U (h : ProtLevel p G H W U U' β κ ξ ζ) {x : V} (hx : x ∈ W) {c : Fin 4}
    (hc : AllowedT F1 (p x) c) :
    ((U.filter fun y => p y = c ∧ ¬ H.Adj x y).card : ℝ) ≤ (ξ + ζ) * W.card := by
  have hsub : U.filter (fun y => p y = c ∧ ¬ H.Adj x y) ⊆
      W.filter (fun y => p y = c ∧ ¬ G.Adj x y) ∪
        W.filter (fun y => G.Adj x y ∧ ¬ H.Adj x y) := by
    intro y hy
    obtain ⟨hyU, hyk, hyH⟩ := mem_filter.mp hy
    by_cases hG : G.Adj x y
    · exact mem_union_right _ (mem_filter.mpr ⟨h.hUW hyU, hG, hyH⟩)
    · exact mem_union_left _ (mem_filter.mpr ⟨h.hUW hyU, hyk, hG⟩)
  have hc' : ((U.filter fun y => p y = c ∧ ¬ H.Adj x y).card : ℝ) ≤
      (W.filter (fun y => p y = c ∧ ¬ G.Adj x y)).card +
        (W.filter (fun y => G.Adj x y ∧ ¬ H.Adj x y)).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have := h.htyp x hx c hc
  have := h.hdam x hx
  linarith

/-- **Lower class count of a cross neighbourhood.** -/
theorem tgt_cls_lower (h : ProtLevel p G H W U U' β κ ξ ζ) {R : Finset (Sym2 V)} {ρ ε' : ℝ}
    (hR : CrossResGood p H W U R ρ ε') (hρ : 0 ≤ ρ) (E : Finset (Sym2 V)) {r : V}
    (hr : r ∈ W) (hrU : r ∉ U) {c : Fin 4} (hc : AllowedT F1 (p r) c) :
    ρ * (((U.filter fun z => p z = c).card : ℝ) - (ξ + ζ) * W.card) - ε' * W.card ≤
      ((tgt U (R ∪ E) r).filter fun z => p z = c).card := by
  have h4 := abs_le.mp (hR.r4 r hr hrU c)
  have hsplit := card_filter_add_card_filter_not (s := U.filter fun z => p z = c)
    (fun z => H.Adj r z)
  have hA : ((U.filter fun z => p z = c).filter (fun z => H.Adj r z)) =
      U.filter fun z => p z = c ∧ H.Adj r z := by rw [filter_filter]
  have hB : ((U.filter fun z => p z = c).filter (fun z => ¬ H.Adj r z)) =
      U.filter fun y => p y = c ∧ ¬ H.Adj r y := by rw [filter_filter]
  rw [hA, hB] at hsplit
  have hm := miss_U h hr hc
  have hs : ((U.filter fun z => p z = c ∧ H.Adj r z).card : ℝ) ≥
      ((U.filter fun z => p z = c).card : ℝ) - (ξ + ζ) * W.card := by
    have : ((U.filter fun z => p z = c ∧ H.Adj r z).card : ℝ) +
        (U.filter fun y => p y = c ∧ ¬ H.Adj r y).card = (U.filter fun z => p z = c).card := by
      exact_mod_cast hsplit
    linarith
  have hsub : U.filter (fun z => p z = c ∧ H.Adj r z ∧ s(r, z) ∈ R) ⊆
      (tgt U (R ∪ E) r).filter fun z => p z = c := by
    intro z hz
    obtain ⟨hzU, hzc, -, hzR⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hzU, mem_union_left _ hzR⟩, hzc⟩
  have hc2 : ((U.filter fun z => p z = c ∧ H.Adj r z ∧ s(r, z) ∈ R).card : ℝ) ≤
      ((tgt U (R ∪ E) r).filter fun z => p z = c).card := by exact_mod_cast card_le_card hsub
  nlinarith [mul_le_mul_of_nonneg_left hs hρ]

/-- **Upper class count of a cross neighbourhood.** -/
theorem tgt_cls_upper {R : Finset (Sym2 V)} {ρ ε' : ℝ}
    (hR : CrossResGood p H W U R ρ ε') (hρ : 0 ≤ ρ) (E : Finset (Sym2 V)) {r : V}
    (hr : r ∈ W) (hrU : r ∉ U) (c : Fin 4) :
    (((tgt U (R ∪ E) r).filter fun z => p z = c).card : ℝ) ≤
      ρ * (U.filter fun z => p z = c).card + ε' * W.card + (E.filter fun e => r ∈ e).card := by
  have h4 := abs_le.mp (hR.r4 r hr hrU c)
  have hsub : (tgt U (R ∪ E) r).filter (fun z => p z = c) ⊆
      (U.filter fun z => p z = c ∧ H.Adj r z ∧ s(r, z) ∈ R) ∪
        (U.filter fun z => s(r, z) ∈ E) := by
    intro z hz
    simp only [tgt, mem_filter, mem_union] at hz ⊢
    obtain ⟨⟨hzU, hRE⟩, hzc⟩ := hz
    rcases hRE with hzR | hzE
    · exact Or.inl ⟨hzU, hzc, SimpleGraph.mem_edgeFinset.mp (hR.sub hzR), hzR⟩
    · exact Or.inr ⟨hzU, hzE⟩
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hc' : (((tgt U (R ∪ E) r).filter fun z => p z = c).card : ℝ) ≤
      (U.filter fun z => p z = c ∧ H.Adj r z ∧ s(r, z) ∈ R).card +
        (U.filter fun z => s(r, z) ∈ E).card := by exact_mod_cast hc
  have hmono : ((U.filter fun z => p z = c ∧ H.Adj r z).card : ℝ) ≤
      (U.filter fun z => p z = c).card := by
    exact_mod_cast card_le_card (fun z hz => by
      simp only [mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.1⟩)
  have := nbrU_le_deg U E r
  nlinarith [mul_le_mul_of_nonneg_left hmono hρ]

/-- **Link defect of a cross neighbourhood** w.r.t. the internal reserve
`E(H[U]) \ E(H[U'])`, from the physical bad-set query. -/
theorem tgt_defect (h : ProtLevel p G H W U U' β κ ξ ζ) {R : Finset (Sym2 V)} {ρ ε : ℝ}
    (hρ : 0 ≤ ρ)
    (hbad : ∀ x ∈ W, ∀ v ∈ W, ∀ c : Fin 4,
      ((U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ H.Adj v z) ∧ s(x, z) ∈ R).card : ℝ) ≤
        ρ * (U'.card + (U.filter fun z => p z = c ∧ ¬ H.Adj v z).card) + ε * W.card)
    (E : Finset (Sym2 V)) {r v : V} (hr : r ∈ W) (hv : v ∈ U) {c : Fin 4}
    (hc : AllowedT F1 (p v) c) :
    (((tgt U (R ∪ E) r).filter fun z => p z = c ∧
        ¬ (z ≠ v ∧ s(v, z) ∈ edgesIn H U \ edgesIn H U')).card : ℝ) ≤
      1 + ρ * (U'.card + ξ * W.card) + ε * W.card + (E.filter fun e => r ∈ e).card := by
  have hsub : (tgt U (R ∪ E) r).filter (fun z => p z = c ∧
        ¬ (z ≠ v ∧ s(v, z) ∈ edgesIn H U \ edgesIn H U')) ⊆
      ({v} ∪ U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ H.Adj v z) ∧ s(r, z) ∈ R) ∪
        (U.filter fun z => s(r, z) ∈ E) := by
    intro z hz
    simp only [tgt, mem_filter, mem_union] at hz
    obtain ⟨⟨hzU, hRE⟩, hzc, hnot⟩ := hz
    by_cases hzv : z = v
    · exact mem_union_left _ (mem_union_left _ (mem_singleton.mpr hzv))
    have hbadz : z ∈ U' ∨ ¬ H.Adj v z := by
      by_contra hcon
      push_neg at hcon
      apply hnot
      refine ⟨hzv, mem_sdiff.mpr ⟨?_, ?_⟩⟩
      · simp only [edgesIn, mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
          mk_all_mem]
        exact ⟨hcon.2, hv, hzU⟩
      · simp only [edgesIn, mem_filter, mk_all_mem]
        exact fun h' => hcon.1 h'.2.2
    rcases hRE with hzR | hzE
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hzU, hzc, hbadz, hzR⟩))
    · exact mem_union_right _ (mem_filter.mpr ⟨hzU, hzE⟩)
  have hcard := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  rw [card_singleton] at hcard
  have hcard' : (((tgt U (R ∪ E) r).filter fun z => p z = c ∧
        ¬ (z ≠ v ∧ s(v, z) ∈ edgesIn H U \ edgesIn H U')).card : ℝ) ≤
      1 + (U.filter fun z => p z = c ∧ (z ∈ U' ∨ ¬ H.Adj v z) ∧ s(r, z) ∈ R).card +
        (U.filter fun z => s(r, z) ∈ E).card := by exact_mod_cast hcard
  have hb := hbad r hr v (h.hUW hv) c
  have hmiss : ((U.filter fun z => p z = c ∧ ¬ H.Adj v z).card : ℝ) ≤ ξ * W.card := by
    refine le_trans ?_ (h.htyp v (h.hUW hv) c hc)
    apply Nat.cast_le.mpr
    apply card_le_card
    intro z hz
    obtain ⟨hzU, hzc, hzH⟩ := mem_filter.mp hz
    exact mem_filter.mpr ⟨h.hUW hzU, hzc, fun hG => hzH (h.hprot v hv z hzU hG)⟩
  have := nbrU_le_deg U E r
  nlinarith [mul_le_mul_of_nonneg_left hmiss hρ]

/-- **Pairwise overlap of two cross neighbourhoods.** -/
theorem tgt_overlap {R : Finset (Sym2 V)} {ρ ε' : ℝ}
    (hR : CrossResGood p H W U R ρ ε') (E : Finset (Sym2 V)) {a b : V}
    (ha : a ∈ W) (hb : b ∈ W) (hab : a ≠ b) (haU : a ∉ U) (hbU : b ∉ U) :
    ((tgt U (R ∪ E) a ∩ tgt U (R ∪ E) b).card : ℝ) ≤
      ρ ^ 2 * U.card + 4 * ε' * W.card + (E.filter fun e => a ∈ e).card +
        (E.filter fun e => b ∈ e).card := by
  set S := U.filter fun z => s(a, z) ∈ R ∧ s(b, z) ∈ R with hS
  have hsub : tgt U (R ∪ E) a ∩ tgt U (R ∪ E) b ⊆
      (S ∪ U.filter fun z => s(a, z) ∈ E) ∪ U.filter fun z => s(b, z) ∈ E := by
    intro z hz
    simp only [tgt, mem_inter, mem_filter, mem_union] at hz
    obtain ⟨⟨hzU, ha'⟩, -, hb'⟩ := hz
    rcases ha' with haR | haE
    · rcases hb' with hbR | hbE
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hzU, haR, hbR⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hzU, hbE⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hzU, haE⟩))
  have hc := (card_le_card hsub).trans ((card_union_le _ _).trans
    (Nat.add_le_add_right (card_union_le _ _) _))
  have hc' : ((tgt U (R ∪ E) a ∩ tgt U (R ∪ E) b).card : ℝ) ≤
      S.card + (U.filter fun z => s(a, z) ∈ E).card +
        (U.filter fun z => s(b, z) ∈ E).card := by exact_mod_cast hc
  -- the fully reserved part, class by class
  have hcls : ∀ l : Fin 4, ((S.filter fun z => p z = l).card : ℝ) ≤
      ρ ^ 2 * (U.filter fun z => p z = l).card + ε' * W.card := by
    intro l
    have h3 := abs_le.mp (hR.r3 a ha b hb hab haU hbU l)
    have heq : S.filter (fun z => p z = l) =
        U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z ∧ s(a, z) ∈ R ∧ s(b, z) ∈ R := by
      ext z
      simp only [hS, mem_filter]
      constructor
      · rintro ⟨⟨hzU, haR, hbR⟩, hzl⟩
        exact ⟨hzU, hzl, SimpleGraph.mem_edgeFinset.mp (hR.sub haR),
          SimpleGraph.mem_edgeFinset.mp (hR.sub hbR), haR, hbR⟩
      · rintro ⟨hzU, hzl, -, -, haR, hbR⟩; exact ⟨⟨hzU, haR, hbR⟩, hzl⟩
    rw [heq]
    have hmono : ((U.filter fun z => p z = l ∧ H.Adj a z ∧ H.Adj b z).card : ℝ) ≤
        (U.filter fun z => p z = l).card := by
      exact_mod_cast card_le_card (fun z hz => by
      simp only [mem_filter] at hz ⊢; exact ⟨hz.1, hz.2.1⟩)
    nlinarith [mul_le_mul_of_nonneg_left hmono (sq_nonneg ρ)]
  have hSsum := sum_card_classes p S
  have hUsum := sum_card_classes p U
  have h0 := hcls 0
  have h1 := hcls 1
  have h2 := hcls 2
  have h3 := hcls 3
  have := nbrU_le_deg U E a
  have := nbrU_le_deg U E b
  nlinarith

/-- **Apex candidates of an outer pair**, for every cross graph containing the reserve. -/
theorem apex_count_lower (h : ProtLevel p G H W U U' β κ ξ ζ) {R Q : Finset (Sym2 V)}
    {ρ ε' : ℝ} (hW : 0 < W.card) (hβ : β ≤ 1 / 2) (hκ : 0 ≤ κ) (hξ : 0 ≤ ξ) (hζ : 0 ≤ ζ)
    (hR : CrossResGood p H W U R ρ ε') (hRQ : R ⊆ Q)
    {x y : V} (hx : x ∈ W) (hy : y ∈ W) (hxy : x ≠ y) (hxU : x ∉ U) (hyU : y ∉ U)
    (hall : AllowedT F1 (p x) (p y)) :
    ρ ^ 2 * (uOf U - κ * W.card - 2 * ξ * W.card - 2 * ζ * W.card) - ε' * W.card ≤
      ((U.filter fun z => s(x, z) ∈ Q ∧ s(y, z) ∈ Q ∧
        ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1).card : ℝ) := by
  have hthird : ∀ i j : Fin 4, AllowedT F1 i j → ∃ l : Fin 4, ({i, j, l} : Multiset (Fin 4)) ∈ F1 := by
    decide
  obtain ⟨l, hl⟩ := hthird _ _ hall
  have hlow := apex_supply_lower (h.levelHyp hW hβ hκ hξ hζ) hR hx hy hxy hxU hyU hl
  have hin := (abs_le.mp (h.hin l)).1
  have hmono : ((U.filter fun z => s(x, z) ∈ R ∧ s(y, z) ∈ R ∧
      ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1).card : ℝ) ≤
      ((U.filter fun z => s(x, z) ∈ Q ∧ s(y, z) ∈ Q ∧
        ({p x, p y, p z} : Multiset (Fin 4)) ∈ F1).card : ℝ) := by
    exact_mod_cast card_le_card (fun z hz => by
      simp only [mem_filter] at hz ⊢; exact ⟨hz.1, hRQ hz.2.1, hRQ hz.2.2.1, hz.2.2.2⟩)
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  nlinarith [mul_le_mul_of_nonneg_left hin hρ2]

end Counts

/-- **Visit load of a child vertex**: at most its degree in the cross graph. -/
theorem visits_le (U : Finset V) (Q : Finset (Sym2 V)) (kr : ℕ) (r : ℕ → V)
    (hr : ∀ i < kr, ∀ j < kr, r i = r j → i = j) (v : V) :
    visits (fun j => tgt U Q (r j)) kr v ≤ (Q.filter fun e => v ∈ e).card := by
  unfold visits
  have hd := deg_eq_card_nbrs Q v
  unfold SpreadGen.deg at hd
  rw [hd]
  apply card_le_card_of_injOn r
  · intro j hj
    simp only [coe_filter, mem_range, Set.mem_setOf_eq, tgt, mem_filter] at hj
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    rw [Sym2.eq_swap]; exact hj.2.2
  · intro i hi j hj hij
    simp only [coe_filter, mem_range, Set.mem_setOf_eq] at hi hj
    exact hr i hi.1 j hj.1 hij

end NashWilliams18.SpreadF1
