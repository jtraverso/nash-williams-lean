/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SelectedTripleCutStage98
public import PartitionedTriangleAbsorption.CleanupInductionStage100

/-! # A private absorber produced by the complete physical chain

The target partition and the terminal decomposition are outputs, not inputs.
The first bridge retains catalyst freshness, needed when they are discarded
in the backwards assembly. This is a private, residue-dependent absorber.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PrivateAbsorberStage101

open Finset ColouredHub TripleCutStage94 TypedTransformer AntiEdgeSelection
  CatalystInsertionStage89 PhysicalMovesStage86 SelectedTripleCutStage98 CleanupStage100
  PairMoveAssemblyStage85

variable {V : Type*} [DecidableEq V] [Fintype V] {t : ℕ}

/-- Retain freshness against the initial used edges in the selected cut.
This strengthens the output interface without changing frozen Stage98. -/
theorem fresh_selected_cut {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hF : ThreeStepLinks F) (hcard : ∀ τ ∈ F, τ.card = 3)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v)) (c : Multiset (Fin t) → ℕ)
    (hvec : edgeVec p X = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ)
    (hb : (Z.card : ℝ) + 272 * X.card + 4 * (d + U.card) < a) :
    ∃ (S : Data V) (Z₀ : Finset V) (pos : Tok V → Sym2 V)
      (U' : Finset (Sym2 V)) (Z' : Finset V) (n : ℕ),
      S.Y.card = X.card ∧ S.A.card = X.card ∧
      Frame p F G B S Z₀ ∧ HasDecomp p F S.cats ∧
      S.cats ⊆ G.edgeFinset ∧ Disjoint S.cats B ∧ Disjoint S.cats U ∧
      S.cats.card ≤ 3 * X.card ∧
      Phys p F G B S.tokens pos U' Z' ∧ Bdry p F S pos ∅ ∧
      U'.card ≤ U.card + 66 * X.card ∧ Z'.card ≤ Z.card + 8 * X.card ∧ n ≤ 7 * X.card ∧
      PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) (S.tokens.image pos) n ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos) W k →
        PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) W (n + k) := by
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  obtain ⟨S, L, m, cz, cz', U₂, Z₂, hm, _, _, _, hYc, hYvec, _, hAc, hUL, _, hLc, _,
      hdec, hDG, hDBL, hDc, fr, inv, hU₂, htr, hcont, _⟩ :=
    TypedCatalystBridgeStage93.catalyst_producer G a d hF hs B U X Z hB hd hXU hXG hXB hZ
      hact heven (by linarith)
  have hAX : S.A.card = X.card := hAc.trans hYc
  have hU₂c : U₂.card ≤ U.card + 39 * X.card := by
    have h1 := card_union_le L S.cats
    omega
  have hZcut : (Z ∪ S.A ∪ CatalystSelectionStage89.catVertsAll S.A S.co S.cs S.ct ∪
      S.carriers cz cz').card ≤ Z.card + 6 * X.card := by
    have h1 := card_union_le
      (Z ∪ S.A ∪ CatalystSelectionStage89.catVertsAll S.A S.co S.cs S.ct) (S.carriers cz cz')
    have h2 := card_union_le (Z ∪ S.A) (CatalystSelectionStage89.catVertsAll S.A S.co S.cs S.ct)
    have h3 := card_union_le Z S.A
    have h4 := CatalystSelectionStage89.catVertsAll_card_le S.A S.co S.cs S.ct
    have h5 := carriers_card_le (S := S) (cz := cz) (cz' := cz')
    omega
  have hZr : ((Z ∪ S.A ∪ CatalystSelectionStage89.catVertsAll S.A S.co S.cs S.ct ∪
      S.carriers cz cz').card : ℝ) ≤ Z.card + 6 * X.card := by exact_mod_cast hZcut
  have hUr : (U₂.card : ℝ) ≤ U.card + 39 * X.card := by exact_mod_cast hU₂c
  have hYr : (S.Y.card : ℝ) = X.card := by exact_mod_cast hYc
  obtain ⟨pos', U', Z', r, hr, ph, bd, _, _, hUc, _, hZc, tr, cont⟩ :=
    cut_from_coefficients a d hF hcard hs hB hd (initial_phys fr inv) (initial_bdry fr inv)
      c (hYvec.trans hvec) (by rw [hYr]; linarith)
  have cfg := S.config_eq_image cz cz' S.A
  refine ⟨S, _, pos', U', Z', m + 3 * S.A.card + 9 * r,
    hYc, hAX, fr, hdec, hDG, hDBL.mono_right subset_union_left,
    (hDBL.mono_right subset_union_right).mono_right hUL, ?_, ph, bd,
    ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · omega
  · omega
  · have h := hcont _ _ (cfg ▸ tr)
    simpa only [Nat.add_assoc] using h
  · intro W k hW
    have h := hcont _ _ (cfg ▸ cont W k hW)
    simpa only [Nat.add_assoc] using h

/-- Nonnegative type coefficients produce a genuine private absorber.
Neither a trace nor a decomposition of its terminal configuration is assumed. -/
theorem private_absorber_of_nonnegative_coefficients
    {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ)
    (hF : ThreeStepLinks F) (hcard : ∀ τ ∈ F, τ.card = 3)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B P : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hPG : P ⊆ G.edgeFinset) (hPB : Disjoint P B)
    (hZ : ∀ e ∈ P, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ P → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad P v)) (c : Multiset (Fin t) → ℕ)
    (hvec : edgeVec p P = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ)
    (hb : (Z.card : ℝ) + 382 * P.card + 4 * (d + P.card) < a) :
    ∃ A, Absorbs (p := p) (F := F) A P ∧ Disjoint A B ∧
      A.card ≤ 93 * P.card ∧ A ⊆ G.edgeFinset := by
  have hP0 : (0 : ℝ) ≤ P.card := Nat.cast_nonneg _
  obtain ⟨S, Z₀, pos, U, Z', n, hY, hA, fr, hD, hDG, hDB, hDP, hDc,
      ph, bd, hUc, hZc, hn, _, cont⟩ :=
    fresh_selected_cut G a d hF hcard hs B P P Z hB hd (Subset.refl _) hPG hPB hZ
      hact heven c hvec (by linarith)
  have hUr : (U.card : ℝ) ≤ P.card + 66 * P.card := by exact_mod_cast hUc
  have hZr : (Z'.card : ℝ) ≤ Z.card + 8 * P.card := by exact_mod_cast hZc
  have hAr : (S.A.card : ℝ) = P.card := by exact_mod_cast hA
  obtain ⟨pos', U', Z'', m, _, _, _, dec, _, _, _, _, _, _, hm, tr, _⟩ :=
    cleanup_all a d hF hs hB hd ph bd fr.link (by rw [hAr]; linarith)
  obtain ⟨A, habs, hAB, hAc, hAG⟩ :=
    private_absorber_of_physical_trace hDP.symm hDB hDG hD (cont _ _ tr) dec
  refine ⟨A, habs, hAB, ?_, hAG⟩
  omega

end PartitionedTriangleAbsorption.PrivateAbsorberStage101
