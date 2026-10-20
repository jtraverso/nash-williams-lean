/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutInvariantStage94

/-! # Cutting one prescribed triple of original tokens

`cut_triple` is the producer for one triple. Three distinct remaining
original tokens `e₁, e₂, e₃` with endpoint-label types `(i,j)`, `(j,k)`,
`(k,i)` and `{i,j,k} ∈ F` are given. Their six current endpoints are carriers
(boundary invariant), hence pairwise distinct and distinct from their six
catalytic endpoints; these are the twelve distinct roots of
`three_exchanges`. The result:

* an actual allowed triangle `z_A z_B z_C` formed by `e₁, e₂, e₃`, with its
  decomposition, isolated as a component (`TriangleCut`);
* the boundary invariant for the remaining tokens `R \ {e₁, e₂, e₃}`;
* all other original tokens and all `(y, 2)` catalytic tokens unchanged;
* a physical trace of exactly nine moves, ledger growth at most `81`,
  active-set growth at most `6`, and a continuation from the final ledger.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer CatalystInsertionStage89 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The finished triangle of one cut: the three original tokens form the
actual allowed triangle `z_A z_B z_C`, and no other token touches it. -/
structure TriangleCut (p : V → Fin t) (F : Finset (Multiset (Fin t))) (S : Data V)
    (pos : Tok V → Sym2 V) (e₁ e₂ e₃ : Sym2 V) (i j k : Fin t) (zA zB zC : V) : Prop where
  ne : zA ≠ zB ∧ zA ≠ zC ∧ zB ≠ zC
  label : p zA = i ∧ p zB = j ∧ p zC = k
  pos₁ : pos (.inl e₁) = s(zA, zB)
  pos₂ : pos (.inl e₂) = s(zB, zC)
  pos₃ : pos (.inl e₃) = s(zC, zA)
  decomp : HasDecomp p F {s(zA, zB), s(zB, zC), s(zC, zA)}
  atA : tokAtP S pos zA = {.inl e₃, .inl e₁}
  atB : tokAtP S pos zB = {.inl e₁, .inl e₂}
  atC : tokAtP S pos zC = {.inl e₂, .inl e₃}

omit [DecidableEq V] in
/-- A catalytic token at a carrier `v` is not the catalytic token at a
different carrier `X`. -/
theorem tok_ne_of {S : Data V} {pos : Tok V → Sym2 V} {y y' v X : V} {i i' : Fin 3}
    (hp : pos (.inr (y, i)) = s(v, catV S y i))
    (hX : pos (.inr (y', i')) = s(X, catV S y' i')) (hvX : v ≠ X) :
    (.inr (y, i) : Tok V) ≠ .inr (y', i') := by
  intro h
  simp only [Sum.inr.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rw [hp] at hX
  exact hvX (Sym2.congr_left.mp hX)

theorem triangle_edges_eq (zA zB zC : V) :
    ({s(zA, zB), s(zB, zC), s(zC, zA)} : Finset (Sym2 V)) =
      CatalystSelectionStage89.catEdges zA zB zC := by
  ext x
  simp only [CatalystSelectionStage89.catEdges, mem_insert, mem_singleton]
  rw [Sym2.eq_swap (a := zC) (b := zA)]
  tauto

variable [Fintype V]

/-- **One prescribed triple is cut into an isolated allowed triangle.** -/
theorem cut_triple {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} (a d : ℝ)
    (hF : ThreeStepLinks F) (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    {S : Data V} {pos : Tok V → Sym2 V} {R U : Finset (Sym2 V)} {Z : Finset V}
    (ph : Phys p F G B S.tokens pos U Z) (bd : Bdry p F S pos R)
    {e₁ e₂ e₃ : Sym2 V} (h₁ : e₁ ∈ R) (h₂ : e₂ ∈ R) (h₃ : e₃ ∈ R)
    (h12 : e₁ ≠ e₂) (h13 : e₁ ≠ e₃) (h23 : e₂ ≠ e₃)
    {i j k : Fin t} (ty₁ : Sym2.map p e₁ = s(i, j)) (ty₂ : Sym2.map p e₂ = s(j, k))
    (ty₃ : Sym2.map p e₃ = s(k, i)) (hijk : Link F i j k)
    (hb : 234 + (Z.card : ℝ) + 4 * (d + U.card) < a) :
    ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V) (zA zB zC : V),
      Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' (R \ {e₁, e₂, e₃}) ∧
      TriangleCut p F S pos' e₁ e₂ e₃ i j k zA zB zC ∧
      zA ∉ Z ∧ zB ∉ Z ∧ zC ∉ Z ∧
      (∀ e, e ≠ e₁ → e ≠ e₂ → e ≠ e₃ → pos' (.inl e) = pos (.inl e)) ∧
      (∀ y, pos' (.inr (y, 2)) = pos (.inr (y, 2))) ∧
      (∀ v ∈ Z, v ∉ pos (.inl e₁) → v ∉ pos (.inl e₂) → v ∉ pos (.inl e₃) →
        tokAtP S pos' v = tokAtP S pos v) ∧
      Z ⊆ Z' ∧ Z'.card ≤ Z.card + 6 ∧ U ⊆ U' ∧ U'.card ≤ U.card + 81 ∧
      PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos') 9 ∧
      ∀ W m, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W m →
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (9 + m) := by
  have noloop : ∀ q ∈ S.tokens, ∀ u v, pos q = s(u, v) → u ≠ v := by
    intro q hq u v huv
    have hG := ph.real (mem_image.mpr ⟨q, hq, huv⟩)
    have h := G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp hG)
    simpa using h
  obtain ⟨A₁, B₁, pE₁, lA₁, lB₁⟩ := orient ((bd.type e₁ h₁).trans ty₁)
  obtain ⟨B₂, C₂, pE₂, lB₂, lC₂⟩ := orient ((bd.type e₂ h₂).trans ty₂)
  obtain ⟨C₃, A₃, pE₃, lC₃, lA₃⟩ := orient ((bd.type e₃ h₃).trans ty₃)
  have mA₁ : A₁ ∈ pos (.inl e₁) := by rw [pE₁]; exact Sym2.mem_mk_left _ _
  have mB₁ : B₁ ∈ pos (.inl e₁) := by rw [pE₁]; exact Sym2.mem_mk_right _ _
  have mB₂ : B₂ ∈ pos (.inl e₂) := by rw [pE₂]; exact Sym2.mem_mk_left _ _
  have mC₂ : C₂ ∈ pos (.inl e₂) := by rw [pE₂]; exact Sym2.mem_mk_right _ _
  have mC₃ : C₃ ∈ pos (.inl e₃) := by rw [pE₃]; exact Sym2.mem_mk_left _ _
  have mA₃ : A₃ ∈ pos (.inl e₃) := by rw [pE₃]; exact Sym2.mem_mk_right _ _
  obtain ⟨yA₁, hyA₁, iA₁, hiA₁, pA₁, atA₁⟩ := bd.carrier e₁ h₁ A₁ mA₁
  obtain ⟨yB₁, hyB₁, iB₁, hiB₁, pB₁, atB₁⟩ := bd.carrier e₁ h₁ B₁ mB₁
  obtain ⟨yB₂, hyB₂, iB₂, hiB₂, pB₂, atB₂⟩ := bd.carrier e₂ h₂ B₂ mB₂
  obtain ⟨yC₂, hyC₂, iC₂, hiC₂, pC₂, atC₂⟩ := bd.carrier e₂ h₂ C₂ mC₂
  obtain ⟨yC₃, hyC₃, iC₃, hiC₃, pC₃, atC₃⟩ := bd.carrier e₃ h₃ C₃ mC₃
  obtain ⟨yA₃, hyA₃, iA₃, hiA₃, pA₃, atA₃⟩ := bd.carrier e₃ h₃ A₃ mA₃
  set wA₁ := catV S yA₁ iA₁ with hwA₁
  set wB₁ := catV S yB₁ iB₁ with hwB₁
  set wB₂ := catV S yB₂ iB₂ with hwB₂
  set wC₂ := catV S yC₂ iC₂ with hwC₂
  set wC₃ := catV S yC₃ iC₃ with hwC₃
  set wA₃ := catV S yA₃ iA₃ with hwA₃
  have d_A1_B1 : A₁ ≠ B₁ := noloop (.inl e₁) ((mem_tokens_inl _).mpr (bd.rem h₁)) _ _ pE₁
  have d_A1_B2 : A₁ ≠ B₂ := bd.carrier_ne h₁ h₂ h12 mA₁ mB₂
  have d_A1_C2 : A₁ ≠ C₂ := bd.carrier_ne h₁ h₂ h12 mA₁ mC₂
  have d_A1_C3 : A₁ ≠ C₃ := bd.carrier_ne h₁ h₃ h13 mA₁ mC₃
  have d_A1_A3 : A₁ ≠ A₃ := bd.carrier_ne h₁ h₃ h13 mA₁ mA₃
  have d_B1_B2 : B₁ ≠ B₂ := bd.carrier_ne h₁ h₂ h12 mB₁ mB₂
  have d_B1_C2 : B₁ ≠ C₂ := bd.carrier_ne h₁ h₂ h12 mB₁ mC₂
  have d_B1_C3 : B₁ ≠ C₃ := bd.carrier_ne h₁ h₃ h13 mB₁ mC₃
  have d_B1_A3 : B₁ ≠ A₃ := bd.carrier_ne h₁ h₃ h13 mB₁ mA₃
  have d_B2_C2 : B₂ ≠ C₂ := noloop (.inl e₂) ((mem_tokens_inl _).mpr (bd.rem h₂)) _ _ pE₂
  have d_B2_C3 : B₂ ≠ C₃ := bd.carrier_ne h₂ h₃ h23 mB₂ mC₃
  have d_B2_A3 : B₂ ≠ A₃ := bd.carrier_ne h₂ h₃ h23 mB₂ mA₃
  have d_C2_C3 : C₂ ≠ C₃ := bd.carrier_ne h₂ h₃ h23 mC₂ mC₃
  have d_C2_A3 : C₂ ≠ A₃ := bd.carrier_ne h₂ h₃ h23 mC₂ mA₃
  have d_C3_A3 : C₃ ≠ A₃ := noloop (.inl e₃) ((mem_tokens_inl _).mpr (bd.rem h₃)) _ _ pE₃
  have d_A1_wA1 : A₁ ≠ wA₁ := bd.carrier_ne_catV h₁ mA₁ hyA₁ iA₁
  have d_A1_wB1 : A₁ ≠ wB₁ := bd.carrier_ne_catV h₁ mA₁ hyB₁ iB₁
  have d_A1_wB2 : A₁ ≠ wB₂ := bd.carrier_ne_catV h₁ mA₁ hyB₂ iB₂
  have d_A1_wC2 : A₁ ≠ wC₂ := bd.carrier_ne_catV h₁ mA₁ hyC₂ iC₂
  have d_A1_wC3 : A₁ ≠ wC₃ := bd.carrier_ne_catV h₁ mA₁ hyC₃ iC₃
  have d_A1_wA3 : A₁ ≠ wA₃ := bd.carrier_ne_catV h₁ mA₁ hyA₃ iA₃
  have d_B1_wA1 : B₁ ≠ wA₁ := bd.carrier_ne_catV h₁ mB₁ hyA₁ iA₁
  have d_B1_wB1 : B₁ ≠ wB₁ := bd.carrier_ne_catV h₁ mB₁ hyB₁ iB₁
  have d_B1_wB2 : B₁ ≠ wB₂ := bd.carrier_ne_catV h₁ mB₁ hyB₂ iB₂
  have d_B1_wC2 : B₁ ≠ wC₂ := bd.carrier_ne_catV h₁ mB₁ hyC₂ iC₂
  have d_B1_wC3 : B₁ ≠ wC₃ := bd.carrier_ne_catV h₁ mB₁ hyC₃ iC₃
  have d_B1_wA3 : B₁ ≠ wA₃ := bd.carrier_ne_catV h₁ mB₁ hyA₃ iA₃
  have d_B2_wA1 : B₂ ≠ wA₁ := bd.carrier_ne_catV h₂ mB₂ hyA₁ iA₁
  have d_B2_wB1 : B₂ ≠ wB₁ := bd.carrier_ne_catV h₂ mB₂ hyB₁ iB₁
  have d_B2_wB2 : B₂ ≠ wB₂ := bd.carrier_ne_catV h₂ mB₂ hyB₂ iB₂
  have d_B2_wC2 : B₂ ≠ wC₂ := bd.carrier_ne_catV h₂ mB₂ hyC₂ iC₂
  have d_B2_wC3 : B₂ ≠ wC₃ := bd.carrier_ne_catV h₂ mB₂ hyC₃ iC₃
  have d_B2_wA3 : B₂ ≠ wA₃ := bd.carrier_ne_catV h₂ mB₂ hyA₃ iA₃
  have d_C2_wA1 : C₂ ≠ wA₁ := bd.carrier_ne_catV h₂ mC₂ hyA₁ iA₁
  have d_C2_wB1 : C₂ ≠ wB₁ := bd.carrier_ne_catV h₂ mC₂ hyB₁ iB₁
  have d_C2_wB2 : C₂ ≠ wB₂ := bd.carrier_ne_catV h₂ mC₂ hyB₂ iB₂
  have d_C2_wC2 : C₂ ≠ wC₂ := bd.carrier_ne_catV h₂ mC₂ hyC₂ iC₂
  have d_C2_wC3 : C₂ ≠ wC₃ := bd.carrier_ne_catV h₂ mC₂ hyC₃ iC₃
  have d_C2_wA3 : C₂ ≠ wA₃ := bd.carrier_ne_catV h₂ mC₂ hyA₃ iA₃
  have d_C3_wA1 : C₃ ≠ wA₁ := bd.carrier_ne_catV h₃ mC₃ hyA₁ iA₁
  have d_C3_wB1 : C₃ ≠ wB₁ := bd.carrier_ne_catV h₃ mC₃ hyB₁ iB₁
  have d_C3_wB2 : C₃ ≠ wB₂ := bd.carrier_ne_catV h₃ mC₃ hyB₂ iB₂
  have d_C3_wC2 : C₃ ≠ wC₂ := bd.carrier_ne_catV h₃ mC₃ hyC₂ iC₂
  have d_C3_wC3 : C₃ ≠ wC₃ := bd.carrier_ne_catV h₃ mC₃ hyC₃ iC₃
  have d_C3_wA3 : C₃ ≠ wA₃ := bd.carrier_ne_catV h₃ mC₃ hyA₃ iA₃
  have d_A3_wA1 : A₃ ≠ wA₁ := bd.carrier_ne_catV h₃ mA₃ hyA₁ iA₁
  have d_A3_wB1 : A₃ ≠ wB₁ := bd.carrier_ne_catV h₃ mA₃ hyB₁ iB₁
  have d_A3_wB2 : A₃ ≠ wB₂ := bd.carrier_ne_catV h₃ mA₃ hyB₂ iB₂
  have d_A3_wC2 : A₃ ≠ wC₂ := bd.carrier_ne_catV h₃ mA₃ hyC₂ iC₂
  have d_A3_wC3 : A₃ ≠ wC₃ := bd.carrier_ne_catV h₃ mA₃ hyC₃ iC₃
  have d_A3_wA3 : A₃ ≠ wA₃ := bd.carrier_ne_catV h₃ mA₃ hyA₃ iA₃
  have d_wA1_wB1 : wA₁ ≠ wB₁ := bd.catV_ne hyB₁ hiB₁ hyA₁ hiA₁ pA₁ pB₁ d_A1_B1
  have d_wA1_wB2 : wA₁ ≠ wB₂ := bd.catV_ne hyB₂ hiB₂ hyA₁ hiA₁ pA₁ pB₂ d_A1_B2
  have d_wA1_wC2 : wA₁ ≠ wC₂ := bd.catV_ne hyC₂ hiC₂ hyA₁ hiA₁ pA₁ pC₂ d_A1_C2
  have d_wA1_wC3 : wA₁ ≠ wC₃ := bd.catV_ne hyC₃ hiC₃ hyA₁ hiA₁ pA₁ pC₃ d_A1_C3
  have d_wA1_wA3 : wA₁ ≠ wA₃ := bd.catV_ne hyA₃ hiA₃ hyA₁ hiA₁ pA₁ pA₃ d_A1_A3
  have d_wB1_wB2 : wB₁ ≠ wB₂ := bd.catV_ne hyB₂ hiB₂ hyB₁ hiB₁ pB₁ pB₂ d_B1_B2
  have d_wB1_wC2 : wB₁ ≠ wC₂ := bd.catV_ne hyC₂ hiC₂ hyB₁ hiB₁ pB₁ pC₂ d_B1_C2
  have d_wB1_wC3 : wB₁ ≠ wC₃ := bd.catV_ne hyC₃ hiC₃ hyB₁ hiB₁ pB₁ pC₃ d_B1_C3
  have d_wB1_wA3 : wB₁ ≠ wA₃ := bd.catV_ne hyA₃ hiA₃ hyB₁ hiB₁ pB₁ pA₃ d_B1_A3
  have d_wB2_wC2 : wB₂ ≠ wC₂ := bd.catV_ne hyC₂ hiC₂ hyB₂ hiB₂ pB₂ pC₂ d_B2_C2
  have d_wB2_wC3 : wB₂ ≠ wC₃ := bd.catV_ne hyC₃ hiC₃ hyB₂ hiB₂ pB₂ pC₃ d_B2_C3
  have d_wB2_wA3 : wB₂ ≠ wA₃ := bd.catV_ne hyA₃ hiA₃ hyB₂ hiB₂ pB₂ pA₃ d_B2_A3
  have d_wC2_wC3 : wC₂ ≠ wC₃ := bd.catV_ne hyC₃ hiC₃ hyC₂ hiC₂ pC₂ pC₃ d_C2_C3
  have d_wC2_wA3 : wC₂ ≠ wA₃ := bd.catV_ne hyA₃ hiA₃ hyC₂ hiC₂ pC₂ pA₃ d_C2_A3
  have d_wC3_wA3 : wC₃ ≠ wA₃ := bd.catV_ne hyA₃ hiA₃ hyC₃ hiC₃ pC₃ pA₃ d_C3_A3
  have nd : [A₁, B₁, B₂, C₂, C₃, A₃, wA₁, wB₁, wB₂, wC₂, wC₃, wA₃].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, not_false_eq_true, and_true]
    exact ⟨⟨d_A1_B1, d_A1_B2, d_A1_C2, d_A1_C3, d_A1_A3, d_A1_wA1, d_A1_wB1, d_A1_wB2, d_A1_wC2,
        d_A1_wC3, d_A1_wA3⟩,
      ⟨d_B1_B2, d_B1_C2, d_B1_C3, d_B1_A3, d_B1_wA1, d_B1_wB1, d_B1_wB2, d_B1_wC2, d_B1_wC3,
        d_B1_wA3⟩,
      ⟨d_B2_C2, d_B2_C3, d_B2_A3, d_B2_wA1, d_B2_wB1, d_B2_wB2, d_B2_wC2, d_B2_wC3, d_B2_wA3⟩,
      ⟨d_C2_C3, d_C2_A3, d_C2_wA1, d_C2_wB1, d_C2_wB2, d_C2_wC2, d_C2_wC3, d_C2_wA3⟩,
      ⟨d_C3_A3, d_C3_wA1, d_C3_wB1, d_C3_wB2, d_C3_wC2, d_C3_wC3, d_C3_wA3⟩,
      ⟨d_A3_wA1, d_A3_wB1, d_A3_wB2, d_A3_wC2, d_A3_wC3, d_A3_wA3⟩,
      ⟨d_wA1_wB1, d_wA1_wB2, d_wA1_wC2, d_wA1_wC3, d_wA1_wA3⟩,
      ⟨d_wB1_wB2, d_wB1_wC2, d_wB1_wC3, d_wB1_wA3⟩,
      ⟨d_wB2_wC2, d_wB2_wC3, d_wB2_wA3⟩,
      ⟨d_wC2_wC3, d_wC2_wA3⟩,
      d_wC3_wA3⟩
  have tm₁ : (.inl e₁ : Tok V) ∈ S.tokens := (mem_tokens_inl _).mpr (bd.rem h₁)
  have tm₂ : (.inl e₂ : Tok V) ∈ S.tokens := (mem_tokens_inl _).mpr (bd.rem h₂)
  have tm₃ : (.inl e₃ : Tok V) ∈ S.tokens := (mem_tokens_inl _).mpr (bd.rem h₃)
  have tA₁ : (.inr (yA₁, iA₁) : Tok V) ∈ S.tokens := (mem_tokens_inr _ _).mpr hyA₁
  have tB₁ : (.inr (yB₁, iB₁) : Tok V) ∈ S.tokens := (mem_tokens_inr _ _).mpr hyB₁
  have tB₂ : (.inr (yB₂, iB₂) : Tok V) ∈ S.tokens := (mem_tokens_inr _ _).mpr hyB₂
  have tC₂ : (.inr (yC₂, iC₂) : Tok V) ∈ S.tokens := (mem_tokens_inr _ _).mpr hyC₂
  have tC₃ : (.inr (yC₃, iC₃) : Tok V) ∈ S.tokens := (mem_tokens_inr _ _).mpr hyC₃
  have tA₃ : (.inr (yA₃, iA₃) : Tok V) ∈ S.tokens := (mem_tokens_inr _ _).mpr hyA₃
  obtain ⟨zA, zB, zC, z'A, z'B, z'C, pos', U', ⟨hzA, hzB, hzC, hz'A, hz'B, hz'C⟩, ndz,
      ⟨lzA, lz'A, lzB, lz'B, lzC, lz'C⟩, ⟨vE₁, vE₂, vE₃⟩, ⟨vA₁, vB₁, vB₂, vC₂, vC₃, vA₃⟩,
      untouched, ph', hUU', hU', htr, hcont⟩ :=
    three_exchanges a d hF hs hB hd ph tm₁ tm₂ tm₃ tA₁ tB₁ tB₂ tC₂ tC₃ tA₃ nd
      pE₁ pE₂ pE₃ pA₁ pB₁ pB₂ pC₂ pC₃ pA₃ (by rw [lB₂, lB₁]) (by rw [lC₃, lC₂])
      (by rw [lA₁, lA₃]) hb
  obtain ⟨L1, ⟨kA₁, kB₁, kB₂, kC₂, kC₃, kA₃⟩, ⟨nA, nB, nC, n'A, n'B, n'C⟩⟩ :=
    after_cut_local (toks := S.tokens) (pos := pos) (pos' := pos') ph.supp tm₁ tm₂ tm₃
      tA₁ tB₁ tB₂ tC₂ tC₃ tA₃ nd pE₁ pE₂ pE₃ pA₁ pB₁ pB₂ pC₂ pC₃ pA₃ hzA hzB hzC hz'A hz'B
      hz'C ndz vE₁ vE₂ vE₃ vA₁ vB₁ vB₂ vC₂ vC₃ vA₃ untouched atA₁ atB₁ atB₂ atC₂ atC₃ atA₃
  replace nA : tokAtP S pos' zA = {.inl e₃, .inl e₁} := nA
  replace nB : tokAtP S pos' zB = {.inl e₁, .inl e₂} := nB
  replace nC : tokAtP S pos' zC = {.inl e₂, .inl e₃} := nC
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at ndz
  obtain ⟨⟨nAB, nAC, nAA', nAB', nAC'⟩, ⟨nBC, nBA', nBB', nBC'⟩, ⟨nCA', nCB', nCC'⟩,
    ⟨nA'B', nA'C'⟩, nB'C'⟩ := ndz
  -- untouched tokens
  have unO : ∀ e, e ≠ e₁ → e ≠ e₂ → e ≠ e₃ → pos' (.inl e) = pos (.inl e) := by
    intro e c1 c2 c3
    exact untouched _ (by simpa using c1) (by simpa using c2) (by simpa using c3) (by simp)
      (by simp) (by simp) (by simp) (by simp) (by simp)
  have unK : ∀ y ii, (.inr (y, ii) : Tok V) ≠ .inr (yA₁, iA₁) →
      (.inr (y, ii) : Tok V) ≠ .inr (yB₁, iB₁) → (.inr (y, ii) : Tok V) ≠ .inr (yB₂, iB₂) →
      (.inr (y, ii) : Tok V) ≠ .inr (yC₂, iC₂) → (.inr (y, ii) : Tok V) ≠ .inr (yC₃, iC₃) →
      (.inr (y, ii) : Tok V) ≠ .inr (yA₃, iA₃) → pos' (.inr (y, ii)) = pos (.inr (y, ii)) :=
    fun _ _ c1 c2 c3 c4 c5 c6 => untouched _ (by simp) (by simp) (by simp) c1 c2 c3 c4 c5 c6
  have ne2 : ∀ {y y' : V} {ii : Fin 3}, ii ≠ 2 → (.inr (y', 2) : Tok V) ≠ .inr (y, ii) := by
    intro y y' ii hii h
    simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact hii h.2.symm
  have un2 : ∀ y, pos' (.inr (y, 2)) = pos (.inr (y, 2)) := fun y =>
    unK y 2 (ne2 hiA₁) (ne2 hiB₁) (ne2 hiB₂) (ne2 hiC₂) (ne2 hiC₃) (ne2 hiA₃)
  -- old vertices are active, new ones are not
  have notN : ∀ v ∈ Z, v ∉ [zA, zB, zC, z'A, z'B, z'C] := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> contradiction
  have notK : ∀ v, v ≠ A₁ → v ≠ B₁ → v ≠ B₂ → v ≠ C₂ → v ≠ C₃ → v ≠ A₃ →
      v ∉ [A₁, B₁, B₂, C₂, C₃, A₃] := by
    intro v c1 c2 c3 c4 c5 c6
    simp [c1, c2, c3, c4, c5, c6]
  have loc : ∀ v ∈ Z, v ≠ A₁ → v ≠ B₁ → v ≠ B₂ → v ≠ C₂ → v ≠ C₃ → v ≠ A₃ →
      tokAtP S pos' v = tokAtP S pos v := fun v hv c1 c2 c3 c4 c5 c6 =>
    L1 v (notK v c1 c2 c3 c4 c5 c6) (notN v hv)
  have memR' : ∀ {e}, e ∈ R \ {e₁, e₂, e₃} ↔ e ∈ R ∧ e ≠ e₁ ∧ e ≠ e₂ ∧ e ≠ e₃ := by
    intro e; simp
  have doneSub : S.Y \ R ⊆ S.Y \ (R \ {e₁, e₂, e₃}) :=
    sdiff_subset_sdiff (Subset.refl _) sdiff_subset
  have newDone : ∀ {e}, e = e₁ ∨ e = e₂ ∨ e = e₃ → e ∈ S.Y \ (R \ {e₁, e₂, e₃}) := by
    rintro e (rfl | rfl | rfl) <;> simp [bd.rem h₁, bd.rem h₂, bd.rem h₃]
  have catNe : ∀ {e : Sym2 V} {X : V}, e ∈ R → X ∈ pos (.inl e) → ∀ y ∈ S.A,
      S.cs y ≠ X ∧ S.ct y ≠ X := by
    intro e X he hX y hy
    refine ⟨fun h => bd.carrier_ne_catV he hX hy 0 (by rw [catV_zero, h]),
      fun h => bd.carrier_ne_catV he hX hy 1 (by rw [catV_one, h])⟩
  have zcs : ∀ y ∈ S.A, S.cs y ∈ Z ∧ S.ct y ∈ Z := fun y hy =>
    ⟨ph.supp _ ((mem_tokens_inr y 2).mpr hy) _
        (by rw [bd.handle₂ y hy]; exact Sym2.mem_mk_left _ _),
     ph.supp _ ((mem_tokens_inr y 2).mpr hy) _
        (by rw [bd.handle₂ y hy]; exact Sym2.mem_mk_right _ _)⟩
  -- the triangle
  have tri_decomp : HasDecomp p F {s(zA, zB), s(zB, zC), s(zC, zA)} := by
    rw [triangle_edges_eq]
    exact CatalystSelectionStage89.catalyst_decomp nAB nAC nBC
      (by rw [lzA, lzB, lzC, lA₃, lB₁, lC₂]; exact hijk)
  have tri : TriangleCut p F S pos' e₁ e₂ e₃ i j k zA zB zC :=
    ⟨⟨nAB, nAC, nBC⟩, ⟨lzA.trans lA₃, lzB.trans lB₁, lzC.trans lC₂⟩, vE₁,
      by rw [vE₂, Sym2.eq_swap], by rw [vE₃, Sym2.eq_swap], tri_decomp, nA, nB, nC⟩
  have bd' : Bdry p F S pos' (R \ {e₁, e₂, e₃}) := by
    refine ⟨sdiff_subset.trans bd.rem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e he
      obtain ⟨heR, c1, c2, c3⟩ := memR'.mp he
      rw [unO e c1 c2 c3]
      exact bd.type e heR
    · intro e he v hv
      obtain ⟨heR, c1, c2, c3⟩ := memR'.mp he
      rw [unO e c1 c2 c3] at hv
      obtain ⟨y, hy, ii, hii, hp, hat⟩ := bd.carrier e heR v hv
      have hvZ : v ∈ Z := ph.supp _ ((mem_tokens_inl e).mpr (bd.rem heR)) _ hv
      have vA₁' : v ≠ A₁ := bd.carrier_ne heR h₁ c1 hv mA₁
      have vB₁' : v ≠ B₁ := bd.carrier_ne heR h₁ c1 hv mB₁
      have vB₂' : v ≠ B₂ := bd.carrier_ne heR h₂ c2 hv mB₂
      have vC₂' : v ≠ C₂ := bd.carrier_ne heR h₂ c2 hv mC₂
      have vC₃' : v ≠ C₃ := bd.carrier_ne heR h₃ c3 hv mC₃
      have vA₃' : v ≠ A₃ := bd.carrier_ne heR h₃ c3 hv mA₃
      refine ⟨y, hy, ii, hii, ?_, ?_⟩
      · rw [unK y ii (tok_ne_of hp pA₁ vA₁') (tok_ne_of hp pB₁ vB₁') (tok_ne_of hp pB₂ vB₂')
          (tok_ne_of hp pC₂ vC₂') (tok_ne_of hp pC₃ vC₃') (tok_ne_of hp pA₃ vA₃')]
        exact hp
      · rw [loc v hvZ vA₁' vB₁' vB₂' vC₂' vC₃' vA₃']
        exact hat
    · intro y hy
      rw [loc _ (zcs y hy).1 (catNe h₁ mA₁ y hy).1 (catNe h₁ mB₁ y hy).1 (catNe h₂ mB₂ y hy).1
        (catNe h₂ mC₂ y hy).1 (catNe h₃ mC₃ y hy).1 (catNe h₃ mA₃ y hy).1]
      exact bd.at_cs y hy
    · intro y hy
      rw [loc _ (zcs y hy).2 (catNe h₁ mA₁ y hy).2 (catNe h₁ mB₁ y hy).2 (catNe h₂ mB₂ y hy).2
        (catNe h₂ mC₂ y hy).2 (catNe h₃ mC₃ y hy).2 (catNe h₃ mA₃ y hy).2]
      exact bd.at_ct y hy
    · intro y hy ii hii
      obtain ⟨h, hh, lh⟩ := bd.handle y hy ii hii
      by_cases c1 : (.inr (y, ii) : Tok V) = .inr (yA₁, iA₁)
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at c1
        rw [c1.1, c1.2] at hh ⊢
        rw [c1.1] at lh
        rw [pA₁] at hh
        have hA : A₁ = h := Sym2.congr_left.mp hh
        refine ⟨z'A, vA₁, ?_⟩
        rw [lz'A, lA₃, ← lA₁, hA, lh]
      by_cases c2 : (.inr (y, ii) : Tok V) = .inr (yB₁, iB₁)
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at c2
        rw [c2.1, c2.2] at hh ⊢
        rw [c2.1] at lh
        rw [pB₁] at hh
        have hX : B₁ = h := Sym2.congr_left.mp hh
        refine ⟨z'B, vB₁, ?_⟩
        rw [lz'B, hX, lh]
      by_cases c3 : (.inr (y, ii) : Tok V) = .inr (yB₂, iB₂)
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at c3
        rw [c3.1, c3.2] at hh ⊢
        rw [c3.1] at lh
        rw [pB₂] at hh
        have hX : B₂ = h := Sym2.congr_left.mp hh
        refine ⟨z'B, vB₂, ?_⟩
        rw [lz'B, lB₁, ← lB₂, hX, lh]
      by_cases c4 : (.inr (y, ii) : Tok V) = .inr (yC₂, iC₂)
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at c4
        rw [c4.1, c4.2] at hh ⊢
        rw [c4.1] at lh
        rw [pC₂] at hh
        have hX : C₂ = h := Sym2.congr_left.mp hh
        refine ⟨z'C, vC₂, ?_⟩
        rw [lz'C, hX, lh]
      by_cases c5 : (.inr (y, ii) : Tok V) = .inr (yC₃, iC₃)
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at c5
        rw [c5.1, c5.2] at hh ⊢
        rw [c5.1] at lh
        rw [pC₃] at hh
        have hX : C₃ = h := Sym2.congr_left.mp hh
        refine ⟨z'C, vC₃, ?_⟩
        rw [lz'C, lC₂, ← lC₃, hX, lh]
      by_cases c6 : (.inr (y, ii) : Tok V) = .inr (yA₃, iA₃)
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at c6
        rw [c6.1, c6.2] at hh ⊢
        rw [c6.1] at lh
        rw [pA₃] at hh
        have hX : A₃ = h := Sym2.congr_left.mp hh
        refine ⟨z'A, vA₃, ?_⟩
        rw [lz'A, hX, lh]
      exact ⟨h, by rw [unK y ii c1 c2 c3 c4 c5 c6]; exact hh, lh⟩
    · intro y hy
      rw [un2 y]
      exact bd.handle₂ y hy
    · intro v hv
      by_cases hvN : v ∈ [zA, zB, zC, z'A, z'B, z'C]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hvN
        rcases hvN with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inr (Or.inr ⟨e₃, e₁, newDone (by simp), newDone (by simp), h13.symm, nA⟩)
        · exact Or.inr (Or.inr ⟨e₁, e₂, newDone (by simp), newDone (by simp), h12, nB⟩)
        · exact Or.inr (Or.inr ⟨e₂, e₃, newDone (by simp), newDone (by simp), h23, nC⟩)
        · exact Or.inr (Or.inl ⟨(yA₃, iA₃), (yA₁, iA₁),
            fun h => tok_ne_of pA₃ pA₁ (Ne.symm d_A1_A3) (by rw [h]), n'A⟩)
        · exact Or.inr (Or.inl ⟨(yB₁, iB₁), (yB₂, iB₂),
            fun h => tok_ne_of pB₁ pB₂ d_B1_B2 (by rw [h]), n'B⟩)
        · exact Or.inr (Or.inl ⟨(yC₂, iC₂), (yC₃, iC₃),
            fun h => tok_ne_of pC₂ pC₃ d_C2_C3 (by rw [h]), n'C⟩)
      by_cases hvK : v ∈ [A₁, B₁, B₂, C₂, C₃, A₃]
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hvK
        rcases hvK with rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl kA₁
        · exact Or.inl kB₁
        · exact Or.inl kB₂
        · exact Or.inl kC₂
        · exact Or.inl kC₃
        · exact Or.inl kA₃
      have hK := hvK
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hK
      obtain ⟨k1, k2, k3, k4, k5, k6⟩ := hK
      rw [show tokAtP S pos' v = tokAtP S pos v from L1 v hvK hvN]
      have hnot : ∀ e ∈ R, v ∉ pos (.inl e) := by
        intro e heR hve
        by_cases c1 : e = e₁
        · subst c1; rw [pE₁, Sym2.mem_iff] at hve; rcases hve with h | h; exacts [k1 h, k2 h]
        by_cases c2 : e = e₂
        · subst c2; rw [pE₂, Sym2.mem_iff] at hve; rcases hve with h | h; exacts [k3 h, k4 h]
        by_cases c3 : e = e₃
        · subst c3; rw [pE₃, Sym2.mem_iff] at hve; rcases hve with h | h; exacts [k5 h, k6 h]
        exact hv e (memR'.mpr ⟨heR, c1, c2, c3⟩) (by rw [unO e c1 c2 c3]; exact hve)
      rcases bd.other v hnot with h | h | ⟨e, e', he, he', hne, hat⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨e, e', doneSub he, doneSub he', hne, hat⟩)
    · intro e he v hv
      by_cases he3 : e = e₁ ∨ e = e₂ ∨ e = e₃
      · rcases he3 with rfl | rfl | rfl
        · rw [vE₁, Sym2.mem_iff] at hv
          rcases hv with rfl | rfl
          · exact ⟨e₃, newDone (by simp), Ne.symm h13, by rw [nA, pair_comm]⟩
          · exact ⟨e₂, newDone (by simp), Ne.symm h12, nB⟩
        · rw [vE₂, Sym2.mem_iff] at hv
          rcases hv with rfl | rfl
          · exact ⟨e₃, newDone (by simp), Ne.symm h23, nC⟩
          · exact ⟨e₁, newDone (by simp), h12, by rw [nB, pair_comm]⟩
        · rw [vE₃, Sym2.mem_iff] at hv
          rcases hv with rfl | rfl
          · exact ⟨e₁, newDone (by simp), h13, nA⟩
          · exact ⟨e₂, newDone (by simp), h23, by rw [nC, pair_comm]⟩
      · simp only [not_or] at he3
        obtain ⟨c1, c2, c3⟩ := he3
        have heY : e ∈ S.Y := (mem_sdiff.mp he).1
        have heR : e ∉ R := fun h => (mem_sdiff.mp he).2 (memR'.mpr ⟨h, c1, c2, c3⟩)
        rw [unO e c1 c2 c3] at hv
        obtain ⟨e', he', hne, hat⟩ := bd.done_iso e (mem_sdiff.mpr ⟨heY, heR⟩) v hv
        have hvZ : v ∈ Z := ph.supp _ ((mem_tokens_inl e).mpr heY) _ hv
        have hnK : ∀ {X : V} {f : Sym2 V}, f ∈ R → X ∈ pos (.inl f) → v ≠ X := by
          rintro X f hf hX rfl
          have hm : (.inl f : Tok V) ∈ tokAtP S pos v :=
            mem_tokAtP.mpr ⟨(mem_tokens_inl f).mpr (bd.rem hf), hX⟩
          rw [hat] at hm
          simp only [mem_insert, mem_singleton, Sum.inl.injEq] at hm
          rcases hm with rfl | rfl
          · exact heR hf
          · exact (mem_sdiff.mp he').2 hf
        rw [loc v hvZ (hnK h₁ mA₁) (hnK h₁ mB₁) (hnK h₂ mB₂) (hnK h₂ mC₂) (hnK h₃ mC₃)
          (hnK h₃ mA₃)]
        exact ⟨e', doneSub he', hne, hat⟩
    · have hset : S.Y \ (R \ {e₁, e₂, e₃}) = (S.Y \ R) ∪ {e₁, e₂, e₃} := by
        ext e
        simp only [mem_sdiff, mem_union, mem_insert, mem_singleton, not_and, not_not]
        constructor
        · rintro ⟨heY, h⟩
          by_cases heR : e ∈ R
          · exact Or.inr (h heR)
          · exact Or.inl ⟨heY, heR⟩
        · rintro (⟨heY, heR⟩ | rfl | rfl | rfl)
          · exact ⟨heY, fun h => absurd h heR⟩
          · exact ⟨bd.rem h₁, fun _ => Or.inl rfl⟩
          · exact ⟨bd.rem h₂, fun _ => Or.inr (Or.inl rfl)⟩
          · exact ⟨bd.rem h₃, fun _ => Or.inr (Or.inr rfl)⟩
      have himg : (S.Y \ (R \ {e₁, e₂, e₃})).image (fun e => pos' (.inl e)) =
          (S.Y \ R).image (fun e => pos (.inl e)) ∪ {s(zA, zB), s(zB, zC), s(zC, zA)} := by
        rw [hset, image_union]
        congr 1
        · refine image_congr fun e he => ?_
          have heR : e ∉ R := (mem_sdiff.mp he).2
          exact unO e (fun h => heR (h ▸ h₁)) (fun h => heR (h ▸ h₂)) (fun h => heR (h ▸ h₃))
        · rw [image_insert, image_insert, image_singleton, vE₁, vE₂, vE₃,
            Sym2.eq_swap (a := zC) (b := zB), Sym2.eq_swap (a := zA) (b := zC)]
      rw [himg]
      refine bd.done_decomp.union tri_decomp ?_
      rw [disjoint_left]
      intro x hx hxT
      obtain ⟨e, he, rfl⟩ := mem_image.mp hx
      have hq : (.inl e : Tok V) ∈ S.tokens := (mem_tokens_inl e).mpr (mem_sdiff.mp he).1
      simp only [mem_insert, mem_singleton] at hxT
      rcases hxT with h | h | h
      · exact hzA (ph.supp _ hq zA (by rw [h]; exact Sym2.mem_mk_left _ _))
      · exact hzB (ph.supp _ hq zB (by rw [h]; exact Sym2.mem_mk_left _ _))
      · exact hzC (ph.supp _ hq zC (by rw [h]; exact Sym2.mem_mk_left _ _))
  have hZ' : (insert zA (insert z'A (insert zC (insert z'C (insert zB (insert z'B Z)))))).card
      ≤ Z.card + 6 := by
    have h1 := card_insert_le zA (insert z'A (insert zC (insert z'C (insert zB (insert z'B Z)))))
    have h2 := card_insert_le z'A (insert zC (insert z'C (insert zB (insert z'B Z))))
    have h3 := card_insert_le zC (insert z'C (insert zB (insert z'B Z)))
    have h4 := card_insert_le z'C (insert zB (insert z'B Z))
    have h5 := card_insert_le zB (insert z'B Z)
    have h6 := card_insert_le z'B Z
    omega
  refine ⟨pos', U', _, zA, zB, zC, ph', bd', tri, hzA, hzB, hzC, unO, un2, ?_, ?_, hZ', hUU',
    hU', htr, hcont⟩
  · intro v hv n1 n2 n3
    exact loc v hv (fun h => n1 (h ▸ mA₁)) (fun h => n1 (h ▸ mB₁)) (fun h => n2 (h ▸ mB₂))
      (fun h => n2 (h ▸ mC₂)) (fun h => n3 (h ▸ mC₃)) (fun h => n3 (h ▸ mA₃))
  · intro v hv
    simp only [mem_insert]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hv)))))

end PartitionedTriangleAbsorption.TripleCutStage94
