/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.Fixer
public import RequestProject.NW18.Case126.Clean126
public import RequestProject.NW18.Case125.Residual

@[expose] public section

/-!
# The final `F₁`-blowup and the application of Theorem 14.7

For a triangle packing `T` of `G` covering every edge at `A`, the cleaned graph
`G' = residualGraph G A (⋃ T)` lives on `V ∖ A` with the partition `p`.

* `residual_even_degree`, `residual_edgeVec` — `G'` is Eulerian and its edge vector is that of
  `E(G) ∖ ⋃ T`;
* `intSurplus_side_F1` — for an edge set all of whose edges are `F₁`-allowed, the internal surplus
  for `P*` is `E₀₀ + E₁₁ + E₂₂ + E₃₃ − (E₀₂ + E₀₃ + E₁₂ + E₁₃)` (cross-divisibility becomes the
  balance condition of integral `F₁`-divisibility);
* `idealized_126` — `G'` is an idealized `F₁`-blowup;
* `finish_126` — Theorem 14.7 then yields a triangle decomposition of `G`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The cleaned graph is Eulerian. -/
lemma residual_even_degree (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (T : Finset (Finset V)) (hdiv : NashWilliams.IsTriangleDivisible G)
    (hT : IsTrianglePacking G T)
    (hcov : ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ T.biUnion triEdges)
    (a : {x // x ∈ Aᶜ}) : Even ((residualGraph G A (T.biUnion triEdges)).degree a) := by
  set C := T.biUnion triEdges with hCdef
  have hC : C ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT.1 t ht)
  have h1 : (residualGraph G A C).degree a + (C.filter (fun e => a.1 ∈ e)).card = G.degree a.1 :=
    residual_degree G A C hC hcov a
  have h2 := covered_incident_card T (fun t ht => (hT.1 t ht).2) hT.2 a.1
  have h3 := hdiv.2 a.1
  rw [← hCdef] at h2
  obtain ⟨k, hk⟩ := h3
  exact ⟨k - (T.filter (fun t => a.1 ∈ t)).card, by omega⟩

/-- The edge vector of the cleaned graph. -/
lemma residual_edgeVec {t : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V)
    (C : Finset (Sym2 V)) (hcov : ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ C)
    (p : V → Fin t) :
    edgeVec (fun a : {x // x ∈ Aᶜ} => p a.1) (residualGraph G A C).edgeFinset =
      edgeVec p (G.edgeFinset \ C) := by
  rw [← residual_edgeFinset_image G A C hcov, edgeVec_image_injective _ Subtype.val_injective]
  rfl

/-- The per-edge identity behind `intSurplus_side_F1`. -/
lemma surplus_term_F1 (i j : Fin 4) (hij : AllowedT F1 i j) :
    (if side4 i = side4 j then (2 : ℤ) else -1) =
      ((if i = 0 ∧ j = 0 then 1 else 0) + (if j = 0 ∧ i = 0 then 1 else 0)) +
      ((if i = 1 ∧ j = 1 then 1 else 0) + (if j = 1 ∧ i = 1 then 1 else 0)) +
      ((if i = 2 ∧ j = 2 then 1 else 0) + (if j = 2 ∧ i = 2 then 1 else 0)) +
      ((if i = 3 ∧ j = 3 then 1 else 0) + (if j = 3 ∧ i = 3 then 1 else 0)) -
      (((if i = 0 ∧ j = 2 then 1 else 0) + (if j = 0 ∧ i = 2 then 1 else 0)) +
      ((if i = 0 ∧ j = 3 then 1 else 0) + (if j = 0 ∧ i = 3 then 1 else 0)) +
      ((if i = 1 ∧ j = 2 then 1 else 0) + (if j = 1 ∧ i = 2 then 1 else 0)) +
      ((if i = 1 ∧ j = 3 then 1 else 0) + (if j = 1 ∧ i = 3 then 1 else 0))) := by
  revert i j; decide

omit [Fintype V] [DecidableEq V] in
/-- Cross-divisibility of an `F₁`-blowup in terms of the four-partition. -/
lemma intSurplus_side_F1 (p : V → Fin 4) (q : V → Fin 2) (E : Finset (Sym2 V))
    (hE : ∀ x y, s(x, y) ∈ E → q x = side4 (p x) ∧ q y = side4 (p y) ∧ AllowedT F1 (p x) (p y)) :
    intSurplus q E = edgeVec p E 0 0 + edgeVec p E 1 1 + edgeVec p E 2 2 + edgeVec p E 3 3 -
      (edgeVec p E 0 2 + edgeVec p E 0 3 + edgeVec p E 1 2 + edgeVec p E 1 3) := by
  rw [intSurplus_eq_sum]
  unfold edgeVec
  simp only [Finset.sum_apply, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun e he => ?_
  induction e using Sym2.ind with
  | _ x y =>
    obtain ⟨hx, hy, hxy⟩ := hE x y he
    rw [edgeSurp_mk, hx, hy]
    simp only [pairVec, Sym2.lift_mk]
    exact surplus_term_F1 (p x) (p y) hxy

lemma card_subtype_filter (A : Finset V) (P : V → Prop) [DecidablePred P] :
    (univ.filter (fun b : {x // x ∈ Aᶜ} => P b.1)).card = ((univ.filter P) \ A).card := by
  rw [← card_map (Function.Embedding.subtype _)]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply,
    mem_sdiff]
  constructor
  · rintro ⟨b, hb, rfl⟩; exact ⟨hb, mem_compl.mp b.2⟩
  · rintro ⟨hx, hxA⟩; exact ⟨⟨x, mem_compl.mpr hxA⟩, hx, rfl⟩

variable {G : SimpleGraph V} [DecidableRel G.Adj] {p : V → Fin 4} {A : Finset V} {s : ℝ}

/-- The cleaned graph is an idealized `F₁`-blowup. -/
lemma idealized_126 (h : Setup126 G p A s) (C : Finset (Sym2 V))
    (hbl : ∀ x y, G.Adj x y → s(x, y) ∉ C → x ∉ A → y ∉ A → AllowedT F1 (p x) (p y))
    (c ε : ℝ) (hCdeg : ∀ a, a ∉ A → ((C.filter (fun e => a ∈ e)).card : ℝ) ≤ c)
    (hεc : s * Fintype.card V + 1 + c ≤ ε * ((Fintype.card V : ℝ) - A.card))
    (hεcls : 1 + 2 * s * Fintype.card V ≤ ε * Fintype.card V / 4) :
    IsIdealizedT F1 ε (residualGraph G A C) (fun a => p a.1) := by
  have hcardA : (Fintype.card {x // x ∈ Aᶜ} : ℝ) = (Fintype.card V : ℝ) - A.card := by
    rw [Fintype.card_coe, card_compl]
    have : A.card ≤ Fintype.card V := card_le_univ A
    push_cast [this]; ring
  have hcls : ∀ i, ((clsT (fun a : {x // x ∈ Aᶜ} => p a.1) i).card : ℝ) =
      ((clsT p i \ A).card : ℝ) := by
    intro i
    unfold clsT
    rw [card_subtype_filter A (fun x => p x = i)]
  have hclsA : ∀ i, ((clsT p i).card : ℝ) ≤ (clsT p i \ A).card + A.card := by
    intro i; exact_mod_cast card_le_card_sdiff_add_card
  have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
  have hAn : (A.card : ℝ) ≤ Fintype.card V := by exact_mod_cast card_le_univ A
  refine ⟨fun i => ?_, fun a b hab => ?_, fun a j hj => ?_⟩
  · rw [hcls, hcardA]
    have := hclsA i
    have := h.cls_lo i
    have := h.A_card
    rcases le_or_gt 0 (1 - ε) with h1e | h1e
    · have := mul_le_mul_of_nonneg_left (show (Fintype.card V : ℝ) - A.card ≤ Fintype.card V by
        linarith) h1e
      nlinarith
    · have : (1 - ε) * ((Fintype.card V : ℝ) - A.card) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg h1e.le (by linarith)
      have : (0 : ℝ) ≤ (clsT p i \ A).card := Nat.cast_nonneg _
      linarith
  · exact hbl a.1 b.1 hab.1 hab.2 (mem_compl.mp a.2) (mem_compl.mp b.2)
  · rw [hcls, hcardA]
    have haA : a.1 ∉ A := mem_compl.mp a.2
    have hdeg : degT (residualGraph G A C) (fun a : {x // x ∈ Aᶜ} => p a.1) a j =
        ((univ.filter (fun w => G.Adj a.1 w ∧ s(a.1, w) ∉ C ∧ p w = j)) \ A).card := by
      unfold degT
      rw [← card_subtype_filter A (fun w => G.Adj a.1 w ∧ s(a.1, w) ∉ C ∧ p w = j)]
      congr 1; ext b; simp [residualGraph, and_assoc]
    rw [hdeg]
    set S := clsT p j \ A with hS
    have hsub : S ⊆ ((univ.filter (fun w => G.Adj a.1 w ∧ s(a.1, w) ∉ C ∧ p w = j)) \ A) ∪
        ((clsT p j).filter (fun w => ¬ G.Adj a.1 w) ∪ S.filter (fun w => s(a.1, w) ∈ C)) := by
      intro w hw
      simp only [hS, mem_sdiff, clsT, mem_filter, mem_univ, true_and] at hw
      simp only [mem_union, mem_sdiff, mem_filter, mem_univ, true_and, hS, clsT]
      by_cases hadj : G.Adj a.1 w
      · by_cases hC : s(a.1, w) ∈ C
        · exact Or.inr (Or.inr ⟨⟨hw.1, hw.2⟩, hC⟩)
        · exact Or.inl ⟨⟨hadj, hC, hw.1⟩, hw.2⟩
      · exact Or.inr (Or.inl ⟨hw.1, hadj⟩)
    have h1 := (card_le_card hsub).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
    have h2 := card_nonadj_cls_le (G := G) (p := p) a.1 j hj
    have h3 := (card_filter_edge_le S C a.1)
    have h1R : (S.card : ℝ) ≤ ((univ.filter (fun w => G.Adj a.1 w ∧ s(a.1, w) ∉ C ∧ p w = j) \
        A).card : ℝ) + ((abnSet G p a.1).card + 1) + (C.filter (fun e => a.1 ∈ e)).card := by
      have : S.card ≤ (univ.filter (fun w => G.Adj a.1 w ∧ s(a.1, w) ∉ C ∧ p w = j) \ A).card +
          ((abnSet G p a.1).card + 1) + (C.filter (fun e => a.1 ∈ e)).card := by omega
      exact_mod_cast this
    have := h.normal a.1 haA
    have := hCdeg a.1 haA
    linarith

end

/-- **Final step**: Theorem 14.7 applied to the cleaned graph gives a triangle decomposition
of `G`. -/
lemma finish_126 {V : Type} [Fintype V] [DecidableEq V] {ε : ℝ} {n₁ : ℕ}
    (h147 : ∀ (W : Type) [Fintype W] [DecidableEq W] (q : W → Fin 4) (H : SimpleGraph W)
      [DecidableRel H.Adj], n₁ ≤ Fintype.card W → IsIntDiv q F1 H.edgeFinset →
      IsIdealizedT F1 ε H q → HasDecomp q F1 H.edgeFinset)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hdiv : NashWilliams.IsTriangleDivisible G)
    (p : V → Fin 4) (A : Finset V) (T : Finset (Finset V)) (hT : IsTrianglePacking G T)
    (hcov : ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ T.biUnion triEdges)
    (hbl : ∀ x y, G.Adj x y → s(x, y) ∉ T.biUnion triEdges → x ∉ A → y ∉ A →
      AllowedT F1 (p x) (p y))
    (h02 : Even (edgeVec p (G.edgeFinset \ T.biUnion triEdges) 0 2))
    (h03 : Even (edgeVec p (G.edgeFinset \ T.biUnion triEdges) 0 3))
    (h12 : Even (edgeVec p (G.edgeFinset \ T.biUnion triEdges) 1 2))
    (h13 : Even (edgeVec p (G.edgeFinset \ T.biUnion triEdges) 1 3))
    (hsum : edgeVec p (G.edgeFinset \ T.biUnion triEdges) 0 0 +
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) 1 1 +
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) 2 2 +
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) 3 3 =
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) 0 2 +
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) 0 3 +
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) 1 2 +
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) 1 3)
    (hid : IsIdealizedT F1 ε (residualGraph G A (T.biUnion triEdges)) (fun a => p a.1))
    (hn : n₁ ≤ Fintype.card {x // x ∈ Aᶜ}) : NashWilliams.HasTriangleDecomposition G := by
  have hvec := residual_edgeVec G A (T.biUnion triEdges) hcov p
  have hv : ∀ i j, edgeVec (fun a : {x // x ∈ Aᶜ} => p a.1)
      (residualGraph G A (T.biUnion triEdges)).edgeFinset i j =
      edgeVec p (G.edgeFinset \ T.biUnion triEdges) i j := fun i j => by rw [hvec]
  have hint : IsIntDiv (fun a : {x // x ∈ Aᶜ} => p a.1) F1
      (residualGraph G A (T.biUnion triEdges)).edgeFinset :=
    isIntDiv_F1 (fun a b hab => hbl a.1 b.1 hab.1 hab.2 (mem_compl.mp a.2) (mem_compl.mp b.2))
      (residual_even_degree G A T hdiv hT hcov) (by rw [hv]; exact h02) (by rw [hv]; exact h03)
      (by rw [hv]; exact h12) (by rw [hv]; exact h13)
      (by rw [hv, hv, hv, hv, hv, hv, hv, hv]; exact hsum)
  obtain ⟨D, hD⟩ := h147 {x // x ∈ Aᶜ} (fun a => p a.1) (residualGraph G A (T.biUnion triEdges))
    hn hint hid
  exact hasTriangleDecomposition_of_residual G A T hT.1 hT.2 hcov (fun a => p a.1) F1 D hD

end NashWilliams18
