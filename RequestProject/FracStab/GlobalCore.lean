/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.FracStab.GlobalClaims
import RequestProject.FracStab.Normal

/-!
# The global part of Theorem 10.9: setting and the key gadget

`Setting` collects the facts established so far about a graph with a heaviest pair `f₀ ∈ E₂` of
weight `F₀` (Claims 10.9.1 and 10.9.2, the cleaning lemma, and the bound on `S`).

* `nbr2 ρ w` — the pairs `(w, x) ∈ E₂` of weight at least `ρ F₀` (the neighbourhood of `w` in
  the paper's graph `G'`, without removing `S`);
* `degree_le_of_E2` — every vertex in a pair of `E₂` has degree at most `(3/4 + 2t + ε) n`;
* `gadget` (Claim 10.9.3 (ii) + (iv)) — a normal, clean, obtuse vertex outside `S` has about
  `n/2` such neighbours.
-/

namespace NashWilliams.Frac

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (φ : Sym2 V → ℝ)

open Classical in
/-- Common neighbours of `uv` which are `κ`-unclean (on either side). -/
noncomputable def ucSet (κ : ℝ) (u v : V) : Finset V :=
  (cn G u v).filter fun x => IsUnclean G φ κ u v x ∨ IsUnclean G φ κ v u x

open Classical in
omit [DecidableEq V] in
lemma mem_ucSet {κ : ℝ} {u v x : V} :
    x ∈ ucSet G φ κ u v ↔ x ∈ cn G u v ∧ (IsUnclean G φ κ u v x ∨ IsUnclean G φ κ v u x) := by
  unfold ucSet; rw [mem_filter]

open Classical in
/-- Common neighbours of `uv` which are not normal for the bipartition `A`. -/
noncomputable def nnSet (α r : ℝ) (u v : V) (A : Finset V) : Finset V :=
  (cn G u v).filter fun x => ¬ IsNormalV G φ α r u v A x

open Classical in
lemma mem_nnSet {α r : ℝ} {u v : V} {A : Finset V} {x : V} :
    x ∈ nnSet G φ α r u v A ↔ x ∈ cn G u v ∧ ¬ IsNormalV G φ α r u v A x := by
  unfold nnSet; rw [mem_filter]

lemma isNormalV_of_not_mem_nnSet {α r : ℝ} {u v : V} {A : Finset V} {x : V} (hx : x ∈ cn G u v)
    (h : x ∉ nnSet G φ α r u v A) : IsNormalV G φ α r u v A x := by
  by_contra h'
  exact h ((mem_nnSet G φ).2 ⟨hx, h'⟩)

open Classical in
/-- The facts available in the global part of the proof of Theorem 10.9. -/
structure Setting (ε t α r κ s ζ F₀ : ℝ) : Prop where
  hφ : GoodWeighting G φ
  δ : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ G.minDegree
  F₀pos : 0 < F₀
  max : ∀ g ∈ E2 G φ t, negW φ g ≤ F₀
  cn_le : ∀ f ∈ E2 G φ t, ((cn G f.1 f.2).card : ℝ) ≤ (1 / 2 + 2 * t) * Fintype.card V
  bip : ∀ f ∈ E2 G φ t, f ∈ HH G φ F₀ → ∃ A, IsBalBip G φ α f.1 f.2 A
  clean : ∀ f ∈ E2 G φ t, ((ucSet G φ κ f.1 f.2).card : ℝ) < κ * Fintype.card V
  S_le : ((SS G φ t F₀ s).card : ℝ) ≤ ζ * Fintype.card V
  hr : 0 < r
  hαr : α ≤ 4 * r ^ 2
  hα0 : 0 ≤ α
  hα : α ≤ 1 / 100
  hε0 : 0 ≤ ε
  ht0 : 0 ≤ t
  ht : t ≤ 1 / 20
  hκ0 : 0 ≤ κ
  hκ : κ ≤ 1 / 100
  hs : 0 ≤ s

/-- Non-normal vertices (Proposition 10.7), in the form used below. -/
lemma card_NN_le {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {u v : V}
    {A : Finset V} (hA : IsBalBip G φ α u v A) :
    ((nnSet G φ α r u v A).card : ℝ) ≤ α / (2 * r) * Fintype.card V := by
  have h := card_not_normalV_le G φ H.hr hA
  unfold nnSet
  have hc := card_cn_le G u v
  have hr := H.hr
  have : α * (cn G u v).card / (2 * r) ≤ α / (2 * r) * Fintype.card V := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    exact mul_le_mul_of_nonneg_left hc H.hα0
  linarith

open Classical in
/-- The pairs `(w, x) ∈ E₂` of weight at least `ρ F₀`. -/
noncomputable def nbr2 (t F₀ ρ : ℝ) (w : V) : Finset V :=
  univ.filter fun x => (w, x) ∈ E2 G φ t ∧ ρ * F₀ ≤ negW φ (w, x)

open Classical in
/-- The pairs of `Q'` at `v`. -/
noncomputable def qpAt (t F₀ : ℝ) (v : V) : Finset V := univ.filter fun w => (v, w) ∈ Qp G φ t F₀

open Classical in
lemma card_qpAt_lt {t F₀ s : ℝ} {v : V} (hv : v ∉ SS G φ t F₀ s) :
    ((qpAt G φ t F₀ v).card : ℝ) < s * Fintype.card V := by
  unfold SS at hv; unfold qpAt
  simp only [mem_filter, mem_univ, true_and, not_le] at hv
  exact hv

lemma mem_E2_of {t F₀ : ℝ} {x y : V} (hxy : (x, y) ∈ negPairs G φ) (hw : 3 / 4 * F₀ ≤ negW φ (x, y))
    (hq : (x, y) ∉ Qp G φ t F₀) : (x, y) ∈ E2 G φ t := by
  by_contra h
  exact hq (by simp only [Qp, HH, mem_sdiff, mem_filter]; exact ⟨⟨hxy, hw⟩, h⟩)

lemma mem_HH_of_E2 {t F₀ ρ : ℝ} (hρ : 3 / 4 ≤ ρ) (hF : 0 < F₀) {x y : V}
    (h : (x, y) ∈ E2 G φ t) (hw : ρ * F₀ ≤ negW φ (x, y)) : (x, y) ∈ HH G φ F₀ := by
  simp only [HH, mem_filter]
  exact ⟨(mem_sdiff.1 h).1, by nlinarith⟩

lemma E2_subset (t : ℝ) : E2 G φ t ⊆ negPairs G φ := sdiff_subset

omit [DecidableEq V] in
/-- `|N(u) ∖ N(v)| + |N(u) ∩ N(v)| = d(u)`. -/
lemma card_nd_add_cn (u v : V) : (nd G u v).card + (cn G u v).card = G.degree u := by
  rw [← G.card_neighborFinset_eq_degree]
  have h := card_filter_add_card_filter_not (s := G.neighborFinset u) (fun y => ¬ G.Adj v y)
  have e1 : nd G u v = (G.neighborFinset u).filter (fun y => ¬ G.Adj v y) := by
    ext y; simp [nd]
  have e2 : cn G u v = (G.neighborFinset u).filter (fun y => ¬ ¬ G.Adj v y) := by
    ext y; simp [cn]
  rw [e1, e2]; exact h

/-- Negative part bounded by `F₀` for pairs outside `Q'`. -/
lemma negPart_le {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {u z : V}
    (huz : G.Adj u z) (hq : (u, z) ∉ Qp G φ t F₀) : max (-φ s(u, z)) 0 ≤ F₀ := by
  have hF := H.F₀pos
  refine max_le ?_ hF.le
  by_cases hneg : φ s(u, z) < 0
  · by_cases hw : 3 / 4 * F₀ ≤ negW φ (u, z)
    · have := H.max _ (mem_E2_of G φ ((mem_negPairs G φ).2 ⟨huz, hneg⟩) hw hq)
      exact this
    · push_neg at hw; unfold negW at hw; simp (config := { failIfUnchanged := false }) only at hw; linarith
  · push_neg at hneg; linarith

/-- Every vertex of a pair of `E₂` has degree at most `(3/4 + 2t + ε) n`. -/
lemma degree_le_of_E2 {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {x y : V}
    (h : (x, y) ∈ E2 G φ t ∨ (y, x) ∈ E2 G φ t) :
    (G.degree x : ℝ) ≤ (3 / 4 + 2 * t + ε) * Fintype.card V := by
  have hc : ((cn G x y).card : ℝ) ≤ (1 / 2 + 2 * t) * Fintype.card V := by
    rcases h with h | h
    · exact H.cn_le _ h
    · rw [cn_comm]; exact H.cn_le _ h
  have h1 := card_cn_ge_deg G x y
  have h1' : (G.degree x : ℝ) + G.degree y ≤ (cn G x y).card + Fintype.card V := by
    exact_mod_cast h1
  have hv' : (G.minDegree : ℝ) ≤ G.degree y := by exact_mod_cast G.minDegree_le_degree y
  have := H.δ
  linarith

omit [Fintype V] in
/-- Removing the elements of a set `Q` from a filtered set. -/
lemma card_filter_and_not_ge (T : Finset V) (P : V → Prop) [DecidablePred P] (Q : Finset V) :
    ((T.filter P).card : ℝ) - Q.card ≤ ((T.filter fun x => P x ∧ x ∉ Q).card : ℝ) := by
  classical
  have : T.filter P ⊆ (T.filter fun x => P x ∧ x ∉ Q) ∪ Q := by
    intro x hx
    rw [mem_filter] at hx
    rw [mem_union, mem_filter]
    by_cases h : x ∈ Q
    · exact Or.inr h
    · exact Or.inl ⟨hx.1, hx.2, h⟩
  have h2 := (card_le_card this).trans (card_union_le _ _)
  have : ((T.filter P).card : ℝ) ≤ ((T.filter fun x => P x ∧ x ∉ Q).card : ℝ) + Q.card := by
    exact_mod_cast h2
  linarith

open Classical in
/-- Normal partners outside `Q'` (first half of Claim 10.9.3 (ii)): a normal vertex `x ∉ S` has
more than `(c - 1)/2 - r c - s n` normal partners `b` on the other side with `(x, b) ∉ Q'`. -/
lemma card_good_partners {t α r s F₀ : ℝ} {u v : V}
    {A : Finset V} (hA : IsBalBip G φ α u v A) {x : V} (hxN : IsNormalV G φ α r u v A x)
    (hxS : x ∉ SS G φ t F₀ s) :
    ((cn G u v).card : ℝ) / 2 - 1 / 2 - r * (cn G u v).card - s * Fintype.card V <
      (((otherSide G u v A x).filter fun b =>
        NormalPair G φ α u v x b ∧ b ∉ qpAt G φ t F₀ x).card : ℝ) := by
  have h1 := card_normal_partners G φ hA hxN
  have h2 := card_filter_and_not_ge (otherSide G u v A x) (fun b => NormalPair G φ α u v x b)
    (qpAt G φ t F₀ x)
  have h3 := card_qpAt_lt G φ hxS
  linarith

/-- A normal partner outside `Q'` gives a pair of `E₂`. -/
lemma mem_E2_of_normal {ε t α r κ s ζ F₀ lam : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {u v x b : V}
    (hlam : 3 / 4 * F₀ ≤ (1 - α) * (lam * F₀)) (hf : lam * F₀ ≤ negW φ (u, v))
    (hN : NormalPair G φ α u v x b) (hq : b ∉ qpAt G φ t F₀ x) :
    (x, b) ∈ E2 G φ t ∧ (1 - α) * (lam * F₀) ≤ negW φ (x, b) := by
  obtain ⟨hxb, hneg, hw⟩ := hN
  have hα := H.hα
  have hw' : (1 - α) * (lam * F₀) ≤ negW φ (x, b) := by
    unfold negW at hf ⊢; simp (config := { failIfUnchanged := false }) only at hf ⊢; nlinarith
  refine ⟨mem_E2_of G φ ((mem_negPairs G φ).2 ⟨hxb, hneg⟩) (le_trans hlam hw') ?_, hw'⟩
  intro h; exact hq (by simp [qpAt, h])

open Classical in
/-- **The gadget** (Claim 10.9.3 (ii) and (iv)).  Let `f = (u, v) ∈ E₂` have weight at least
`λ F₀`, let `A` be an `α`-balanced bipartition of `f`, and let `w` be a common neighbour which is
normal, not `κ`-unclean, `u`-obtuse with `|φ(vw)| ≥ μ F₀`, with `u, w ∉ S`.  Then `w` lies in at
least `(1/2 - ε - t - r - 3s - κ) n - 1/2` pairs of `E₂` of weight at least `ρ F₀`. -/
theorem gadget {ε t α r κ s ζ F₀ : ℝ} (H : Setting G φ ε t α r κ s ζ F₀) {lam μ ρ : ℝ}
    (hρ1 : ρ ≤ (1 - α) * lam) (hρ2 : ρ ≤ (1 - κ) * (lam + μ) - 1) (hρ3 : 3 / 4 ≤ ρ)
    {u v w : V} (hf : (u, v) ∈ E2 G φ t) (hlam : lam * F₀ ≤ negW φ (u, v)) {A : Finset V}
    (hA : IsBalBip G φ α u v A) (hw : w ∈ cn G u v) (hwS : w ∉ SS G φ t F₀ s)
    (huS : u ∉ SS G φ t F₀ s) (hwN : IsNormalV G φ α r u v A w) (hwc : ¬ IsUnclean G φ κ u v w)
    (huw : 0 < φ s(u, w)) (hvw : μ * F₀ ≤ -φ s(v, w)) :
    (1 / 2 - ε - t - r - 3 * s - κ) * Fintype.card V - 1 / 2 ≤ ((nbr2 G φ t F₀ ρ w).card : ℝ) := by
  have hF := H.F₀pos
  have hα := H.hα
  have hκ := H.hκ
  obtain ⟨huv, hneg⟩ := (mem_negPairs G φ).1 (E2_subset G φ t hf)
  simp (config := { failIfUnchanged := false }) only at huv hneg
  rw [mem_cn] at hw
  -- the two sources of neighbours
  set S1 := (otherSide G u v A w).filter fun b => NormalPair G φ α u v w b ∧ b ∉ qpAt G φ t F₀ w
  set S2 := (nd G u v).filter fun z =>
    (¬ UncleanFor G φ κ u w z ∧ z ∉ qpAt G φ t F₀ w) ∧ z ∉ qpAt G φ t F₀ u
  have hS1 : S1 ⊆ nbr2 G φ t F₀ ρ w := by
    intro b hb
    rw [mem_filter] at hb
    have hlam2 : 3 / 4 * F₀ ≤ (1 - α) * (lam * F₀) := by nlinarith
    obtain ⟨h1, h2⟩ := mem_E2_of_normal G φ H hlam2 hlam hb.2.1 hb.2.2
    simp only [nbr2, mem_filter, mem_univ, true_and]
    exact ⟨h1, by nlinarith⟩
  have huwF : (lam + μ) * F₀ ≤ φ s(u, w) := by
    have := H.hφ.cov u v w huv hw.1 hw.2
    unfold negW at hlam; simp (config := { failIfUnchanged := false }) only at hlam
    nlinarith
  have hS2 : S2 ⊆ nbr2 G φ t F₀ ρ w := by
    intro z hz
    simp only [S2, mem_filter] at hz
    obtain ⟨hznd, ⟨hzc, hzq⟩, hzq'⟩ := hz
    rw [mem_nd] at hznd
    simp only [UncleanFor, not_or, not_lt, not_not] at hzc
    obtain ⟨hwz, hsum⟩ := hzc
    have huz : (u, z) ∉ Qp G φ t F₀ := fun h => hzq' (by simp [qpAt, h])
    have hwq : (w, z) ∉ Qp G φ t F₀ := fun h => hzq (by simp [qpAt, h])
    have hb := negPart_le G φ H hznd.1 huz
    have hmax : ρ * F₀ ≤ max (-φ s(w, z)) 0 := by
      have : (1 - κ) * ((lam + μ) * F₀) ≤ (1 - κ) * φ s(u, w) :=
        mul_le_mul_of_nonneg_left huwF (by linarith)
      nlinarith
    have hpos : 0 < ρ * F₀ := by nlinarith
    have hwz' : ρ * F₀ ≤ -φ s(w, z) := by
      rcases le_total (-φ s(w, z)) 0 with h | h
      · rw [max_eq_right h] at hmax; linarith
      · rw [max_eq_left h] at hmax; exact hmax
    have hzneg : φ s(w, z) < 0 := by linarith
    simp only [nbr2, mem_filter, mem_univ, true_and]
    refine ⟨mem_E2_of G φ ((mem_negPairs G φ).2 ⟨hwz, hzneg⟩) ?_ hwq, hwz'⟩
    unfold negW; simp (config := { failIfUnchanged := false }) only; nlinarith
  have hdisj : Disjoint S1 S2 := by
    rw [disjoint_left]; intro x hx1 hx2
    have h1 := (mem_filter.1 hx1).1
    have h1' := otherSide_subset G hA.1 w h1
    simp only [S2, mem_filter, mem_nd] at hx2
    rw [mem_cn] at h1'
    exact hx2.1.2 h1'.2
  have hsub := card_le_card (union_subset hS1 hS2)
  rw [card_union_of_disjoint hdisj] at hsub
  have hsub' : (S1.card : ℝ) + S2.card ≤ (nbr2 G φ t F₀ ρ w).card := by exact_mod_cast hsub
  -- counting `S1`
  have c1 := card_good_partners G φ hA hwN hwS
  -- counting `S2`
  have hlam1 : lam ≤ 1 := by
    have := H.max _ hf
    by_contra h; push_neg at h; nlinarith
  have hμ : 0 < μ := by
    by_contra h; push_neg at h
    have := H.hκ0
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - κ) (by linarith : (0:ℝ) ≤ 1 - (lam + μ))]
  have hvwneg : φ s(v, w) < 0 := by nlinarith
  have hunc : (((nd G u v).filter fun z => UncleanFor G φ κ u w z).card : ℝ) < κ * Fintype.card V := by
    unfold IsUnclean at hwc
    push_neg at hwc
    exact hwc huw hvwneg
  have e1 := card_filter_add_card_filter_not (s := nd G u v) (fun z => UncleanFor G φ κ u w z)
  have e1' : (((nd G u v).filter fun z => UncleanFor G φ κ u w z).card : ℝ) +
      (((nd G u v).filter fun z => ¬ UncleanFor G φ κ u w z).card : ℝ) = (nd G u v).card := by
    exact_mod_cast e1
  have e2 := card_filter_and_not_ge (nd G u v) (fun z => ¬ UncleanFor G φ κ u w z) (qpAt G φ t F₀ w)
  have e3 := card_filter_and_not_ge (nd G u v)
    (fun z => ¬ UncleanFor G φ κ u w z ∧ z ∉ qpAt G φ t F₀ w) (qpAt G φ t F₀ u)
  have q1 := card_qpAt_lt G φ hwS
  have q2 := card_qpAt_lt G φ huS
  have hnd := card_nd_add_cn G u v
  have hnd' : ((nd G u v).card : ℝ) + (cn G u v).card = G.degree u := by exact_mod_cast hnd
  have hdeg : (G.minDegree : ℝ) ≤ G.degree u := by exact_mod_cast G.minDegree_le_degree u
  have hδ := H.δ
  have hc := H.cn_le _ hf
  have hcn := card_cn_le G u v
  have hr := H.hr
  have hrc : r * ((cn G u v).card : ℝ) ≤ r * Fintype.card V := mul_le_mul_of_nonneg_left hcn hr.le
  simp (config := { failIfUnchanged := false }) only at hc
  have hS2c : ((S2.card : ℕ) : ℝ) = (((nd G u v).filter fun z =>
      (¬ UncleanFor G φ κ u w z ∧ z ∉ qpAt G φ t F₀ w) ∧ z ∉ qpAt G φ t F₀ u).card : ℝ) := rfl
  linarith

end NashWilliams.Frac
