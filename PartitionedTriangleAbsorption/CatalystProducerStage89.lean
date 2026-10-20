/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.CatalystSeparationStage89

/-! # End-to-end producer: deployment, catalyst reservation, insertion

From an even physical configuration `X` we run, in order:

1. the Stage87 deployment to a `0`/`2`-configuration `Y`, with its terminal
   ledger `L` (Stage88-style, keeping the continuation);
2. the catalyst selection outside `B ∪ L`, the active vertices and `Z`;
3. the retrospective framing of the catalysts `D` through the deployment;
4. the token-tracked insertion of all catalysts by Stage87 exchanges, with
   history starting at `L ∪ D` and forbidden vertex set
   `Z ∪ A ∪ (catalyst vertices)`.

The output is an actual physical trace from `X ∪ D` (history `U ∪ D`) to the
final token-tracked configuration, which is 2-regular, plus all the
separation data of `CatalystSeparationStage89`. Explicit budget:
`|Z| + 176 |X| + 4(d + |U|) < a`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.CatalystInsertionStage89

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89 PhysicalMovesStage86
  CatalystFramingStage89

variable {V : Type*} [DecidableEq V] {t : ℕ} [Fintype V]

/-- Each active vertex of a `0`/`2`-configuration has two distinct neighbours. -/
theorem exists_star {Y : Finset (Sym2 V)} {y : V} (hy : y ∈ active Y) :
    ∃ a b : V, a ≠ b ∧ Y.filter (fun e => y ∈ e) = {s(y, a), s(y, b)} := by
  have h2 : (Y.filter fun e => y ∈ e).card = 2 := (mem_filter.mp hy).2
  obtain ⟨e₁, e₂, hne, heq⟩ := card_eq_two.mp h2
  have hm1 : e₁ ∈ Y.filter (fun e => y ∈ e) := by rw [heq]; simp
  have hm2 : e₂ ∈ Y.filter (fun e => y ∈ e) := by rw [heq]; simp
  have h1 : y ∈ e₁ := (mem_filter.mp hm1).2
  have h2' : y ∈ e₂ := (mem_filter.mp hm2).2
  obtain ⟨a, rfl⟩ := Sym2.mem_iff_exists.mp h1
  obtain ⟨b, rfl⟩ := Sym2.mem_iff_exists.mp h2'
  exact ⟨a, b, fun h => hne (h ▸ rfl), heq⟩

/-- Assemble the static insertion frame from the deployment and selection outputs. -/
theorem frame_of_selection {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B L Y : Finset (Sym2 V)} {Z : Finset V}
    {nm np co cs ct : V → V}
    (hstar : ∀ y ∈ active Y, nm y ≠ np y ∧
      Y.filter (fun e => y ∈ e) = {s(y, nm y), s(y, np y)})
    (hdeg : ∀ v, incidentLoad Y v = 0 ∨ incidentLoad Y v = 2)
    (hYG : Y ⊆ G.edgeFinset) (hYB : Disjoint Y B)
    (hact : ∀ u v, s(u, v) ∈ Y → ∃ k, Link F (p u) (p v) k)
    (hc : Catalysts p F G B L (Z ∪ active Y) (active Y) co cs ct) :
    Frame p F G B ⟨Y, active Y, nm, np, co, cs, ct⟩
      (Z ∪ active Y ∪ catVertsAll (active Y) co cs ct) where
  star := fun y hy => (hstar y hy).2
  nm_ne_np := fun y hy => (hstar y hy).1
  supp := fun _ he _ hu => mem_active_of_mem hdeg he hu
  Y_real := hYG
  Y_forb := hYB
  Y_link := hact
  label := hc.label
  link := hc.link
  distinct := hc.distinct
  cat_real := hc.real
  cat_forb := fun y hy => (hc.avoid y hy).mono_right subset_union_left
  notA := fun y hy => (hc.fresh y hy).mono_right subset_union_right
  vdisj := hc.vdisj
  ZA := fun _ hv => mem_union.mpr (Or.inl (mem_union.mpr (Or.inr hv)))
  Zcat := fun y hy _ hv => mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨y, hy, hv⟩))

/-- **End-to-end catalyst producer.** Deployment, fresh physical catalyst
selection outside the full terminal ledger, retrospective framing, and the
token-tracked insertion of all catalysts by actual exchanges. All
quantitative requirements are covered by `|Z| + 176|X| + 4(d + |U|) < a`. -/
theorem catalyst_producer {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v))
    (hb : (Z.card : ℝ) + 176 * X.card + 4 * (d + U.card) < a) :
    ∃ (S : Data V) (L : Finset (Sym2 V)) (m : ℕ) (cz cz' : V → V)
      (U₂ : Finset (Sym2 V)) (Z₂ : Finset V),
      -- deployment
      m ≤ X.card ∧ (∀ v, incidentLoad S.Y v = 0 ∨ incidentLoad S.Y v = 2) ∧
      S.Y ⊆ G.edgeFinset ∧ Disjoint S.Y B ∧ S.Y.card = X.card ∧
      S.A = active S.Y ∧ S.A.card = S.Y.card ∧
      U ⊆ L ∧ S.Y ⊆ L ∧ L.card ≤ U.card + 9 * X.card ∧
      -- catalyst selection
      Catalysts p F G B L (Z ∪ S.A) S.A S.co S.cs S.ct ∧
      HasDecomp p F S.cats ∧ S.cats ⊆ G.edgeFinset ∧ Disjoint S.cats (B ∪ L) ∧
      S.cats.card ≤ 3 * S.Y.card ∧
      -- insertion frame and final invariant
      Frame p F G B S (Z ∪ S.A ∪ catVertsAll S.A S.co S.cs S.ct) ∧
      Inv p F G B S (Z ∪ S.A ∪ catVertsAll S.A S.co S.cs S.ct) cz cz' S.A U₂ Z₂ ∧
      U₂.card ≤ (L ∪ S.cats).card + 27 * S.A.card ∧
      -- the actual trace, deployment followed by insertion
      PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats)
        (S.config cz cz' S.A) (m + 3 * S.A.card) ∧
      (∀ W k, PhysicalMoves p F G.edgeFinset B U₂ (S.config cz cz' S.A) W k →
        PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) W
          (m + (3 * S.A.card + k))) ∧
      -- the final configuration is 2-regular
      (∀ v, incidentLoad (S.config cz cz' S.A) v = 0 ∨
        incidentLoad (S.config cz cz' S.A) v = 2) := by
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  obtain ⟨Y, L, m, co, cs, ct, hm, hdeg, hYG, hYB, hYc, hactY, hUL, hYL, hLc, hc, hAc,
      hdec, hDG, hDBL, hDc, -, hcont⟩ :=
    deploy_reserve_frame G a d hF hs B U X Z hB hd hXU hXG hXB hZ hact heven
      (by linarith)
  have hstar : ∀ y ∈ active Y, ∃ ab : V × V, ab.1 ≠ ab.2 ∧
      Y.filter (fun e => y ∈ e) = {s(y, ab.1), s(y, ab.2)} := by
    intro y hy
    obtain ⟨a, b, hab, h⟩ := exists_star hy
    exact ⟨(a, b), hab, h⟩
  choose! nmp hnmp using hstar
  set S : Data V := ⟨Y, active Y, fun y => (nmp y).1, fun y => (nmp y).2, co, cs, ct⟩ with hS
  have fr : Frame p F G B S (Z ∪ active Y ∪ catVertsAll (active Y) co cs ct) :=
    frame_of_selection (nm := fun y => (nmp y).1) (np := fun y => (nmp y).2)
      (fun y hy => hnmp y hy) hdeg hYG hYB hactY hc
  set Z₀ := Z ∪ active Y ∪ catVertsAll (active Y) co cs ct with hZ₀
  have hZ₀c : (Z₀.card : ℝ) ≤ Z.card + 4 * X.card := by
    have h1 : Z₀.card ≤ (Z ∪ active Y).card + (catVertsAll (active Y) co cs ct).card :=
      card_union_le _ _
    have h2 : (Z ∪ active Y).card ≤ Z.card + (active Y).card := card_union_le _ _
    have h3 := catVertsAll_card_le (active Y) co cs ct
    have : Z₀.card ≤ Z.card + 4 * X.card := by omega
    exact_mod_cast this
  have hU₀c : ((L ∪ S.cats).card : ℝ) ≤ U.card + 12 * X.card := by
    have h1 : (L ∪ S.cats).card ≤ L.card + S.cats.card := card_union_le _ _
    have h2 : S.cats.card ≤ 3 * Y.card := hDc
    have : (L ∪ S.cats).card ≤ U.card + 12 * X.card := by omega
    exact_mod_cast this
  have hAc' : (S.A.card : ℝ) = X.card := by
    change ((active Y).card : ℝ) = X.card
    rw [hAc]; exact_mod_cast hYc
  obtain ⟨cz, cz', U₂, Z₂, inv, hU₂, -, htr, hcont₂⟩ :=
    insert_catalysts a d hF hs hB hd fr (L ∪ S.cats)
      (union_subset_union hYL (Subset.refl _)) (by rw [hAc']; linarith)
  refine ⟨S, L, m, cz, cz', U₂, Z₂, hm, hdeg, hYG, hYB, hYc, rfl, hAc, hUL, hYL, hLc, hc,
    hdec, hDG, hDBL, hDc, fr, inv, hU₂, hcont _ _ htr, fun W k h => hcont _ _ (hcont₂ W k h),
    final_two_regular fr inv.carriers⟩

/-- **Catalytic handles.** In the final configuration the catalytic tokens of
`y` form the path `cz y – cs y – ct y – cz' y`, whose two end carriers both
carry the label `p y` (the label of the processed active vertex). -/
theorem catalytic_handle {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V}
    {Z₀ : Finset V} {cz cz' : V → V} {U : Finset (Sym2 V)} {Z : Finset V}
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z) {y : V} (hy : y ∈ S.A) :
    s(cz y, S.cs y) ∈ S.config cz cz' S.A ∧ s(S.cs y, S.ct y) ∈ S.config cz cz' S.A ∧
      s(cz' y, S.ct y) ∈ S.config cz cz' S.A ∧ p (cz y) = p y ∧ p (cz' y) = p y := by
  have hcat : S.catCur cz cz' S.A y ⊆ S.config cz cz' S.A := fun e he =>
    mem_union.mpr (Or.inr (mem_biUnion.mpr ⟨y, hy, he⟩))
  have hcur : S.catCur cz cz' S.A y = {s(cz y, S.cs y), s(cz' y, S.ct y), s(S.cs y, S.ct y)} := by
    simp [Data.catCur, hy]
  rw [hcur] at hcat
  exact ⟨hcat (by simp), hcat (by simp), hcat (by simp), inv.carrier_label y hy⟩

end PartitionedTriangleAbsorption.CatalystInsertionStage89
