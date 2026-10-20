/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PositiveTargetBridgeStage96
public import PartitionedTriangleAbsorption.TripleCutPartitionStage94

/-! # Cutting the partition selected from nonnegative type coefficients

The slot equivalence produces the actual list consumed by `cut_partition`.
No token partition, physical triangle decomposition or terminal trace is an
input. Catalytic cleanup is deliberately not claimed here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SelectedTripleCutStage98

open Finset ColouredHub TargetTripleSelectionStage95 TripleCutStage94
  TypedTransformer AntiEdgeSelection CatalystInsertionStage89 PhysicalMovesStage86

variable {t : ℕ} {V : Type*} [DecidableEq V]

/-- Three slots read as one target triple, retaining repeated corner labels. -/
noncomputable def target {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (w : Tri F c → Fin 3 → Fin t) (x : Tri F c) :
    TargetTriple V t :=
  ⟨(f (x, 0)).val, (f (x, 1)).val, (f (x, 2)).val, w x 0, w x 1, w x 2⟩

theorem target_toks {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (w : Tri F c → Fin 3 → Fin t) (x : Tri F c) :
    (target f w x).toks = group f x := by
  classical
  ext e
  simp only [TargetTriple.toks, target, group, mem_insert, mem_singleton,
    mem_image, mem_univ, true_and]
  constructor
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · rintro ⟨a, rfl⟩
    fin_cases a <;> simp

omit [DecidableEq V] in
theorem target_valid {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)} (p : V → Fin t)
    (hF : ∀ τ ∈ F, τ.card = 3) (f : Slots F c ≃ Y)
    (hf : ∀ x a, Sym2.map p (f (x, a)).val = slotPair (triWord F hF c) (x, a))
    (x : Tri F c) : (target f (triWord F hF c) x).Valid p F := by
  have ne (a b : Fin 3) (hab : a ≠ b) : (f (x,a)).val ≠ (f (x,b)).val := by
    intro h
    exact hab (congrArg Prod.snd (f.injective (Subtype.ext h)))
  refine ⟨ne 0 1 (by decide), ne 0 2 (by decide), ne 1 2 (by decide),
    ?_, ?_, ?_, ?_⟩
  · simpa [target, slotPair] using hf x 0
  · simpa [target, slotPair] using hf x 1
  · simpa [target, slotPair] using hf x 2
  · exact triWord_mem F hF c x

/-- Enumerate each triangle index once; ordering has no mathematical effect. -/
noncomputable def targets {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (w : Tri F c → Fin 3 → Fin t) : List (TargetTriple V t) := by
  classical
  exact (univ : Finset (Tri F c)).toList.map (target f w)

omit [DecidableEq V] in
theorem targets_valid {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)} (p : V → Fin t)
    (hF : ∀ τ ∈ F, τ.card = 3) (f : Slots F c ≃ Y)
    (hf : ∀ x a, Sym2.map p (f (x, a)).val = slotPair (triWord F hF c) (x, a)) :
    ∀ T ∈ targets f (triWord F hF c), T.Valid p F := by
  classical
  intro T hT
  obtain ⟨x, _, rfl⟩ := List.mem_map.mp hT
  exact target_valid p hF f hf x

theorem targets_pairwise {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (w : Tri F c → Fin 3 → Fin t) :
    (targets f w).Pairwise (fun T T' => Disjoint T.toks T'.toks) := by
  classical
  unfold targets
  rw [List.pairwise_map]
  have hp : (univ : Finset (Tri F c)).toList.Pairwise (fun x y => x ≠ y) :=
    List.nodup_iff_pairwise_ne.mp (nodup_toList _)
  exact hp.imp fun h => by rw [target_toks, target_toks]; exact groups_disjoint f h

theorem allToks_map {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (w : Tri F c → Fin 3 → Fin t) (xs : List (Tri F c)) :
    allToks (xs.map (target f w)) = xs.toFinset.biUnion (group f) := by
  classical
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, allToks_cons, List.toFinset_cons, biUnion_insert,
      target_toks, ih]

theorem targets_cover {F : Finset (Multiset (Fin t))}
    {c : Multiset (Fin t) → ℕ} {Y : Finset (Sym2 V)}
    (f : Slots F c ≃ Y) (w : Tri F c → Fin 3 → Fin t) :
    allToks (targets f w) = Y := by
  classical
  rw [targets, allToks_map]
  ext e
  simpa only [mem_biUnion, List.mem_toFinset, mem_toList] using
    (Finset.ext_iff.mp (groups_cover f) e)

/-- Produce the exact valid partition consumed by the physical cut. -/
theorem exists_partition (p : V → Fin t) (Y : Finset (Sym2 V))
    (F : Finset (Multiset (Fin t))) (hF : ∀ τ ∈ F, τ.card = 3)
    (c : Multiset (Fin t) → ℕ)
    (hvec : edgeVec p Y = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ) :
    ∃ Ts : List (TargetTriple V t),
      (∀ T ∈ Ts, T.Valid p F) ∧
      Ts.Pairwise (fun T T' => Disjoint T.toks T'.toks) ∧
      allToks Ts = Y ∧ 3 * Ts.length = Y.card := by
  classical
  obtain ⟨f, hf⟩ := exists_assignment p Y F hF c hvec
  let Ts := targets f (triWord F hF c)
  have hv := targets_valid p hF f hf
  have hp := targets_pairwise f (triWord F hF c)
  have hc := targets_cover f (triWord F hF c)
  exact ⟨Ts, hv, hp, hc, by rw [← card_allToks hv hp, hc]⟩

variable [Fintype V]

/-- The consumer now receives coefficients, not a supplied target partition. -/
theorem cut_from_coefficients {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} (a d : ℝ)
    (hF : ThreeStepLinks F) (hcard : ∀ τ ∈ F, τ.card = 3)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d) {S : Data V}
    {pos : Tok V → Sym2 V} {U : Finset (Sym2 V)} {Z : Finset V}
    (ph : Phys p F G B S.tokens pos U Z) (bd : Bdry p F S pos S.Y)
    (c : Multiset (Fin t) → ℕ)
    (hvec : edgeVec p S.Y = ∑ τ ∈ F, (c τ : ℤ) • typeEdgeVec τ)
    (hb : (Z.card : ℝ) + 4 * (d + U.card) + 110 * S.Y.card < a) :
    ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V)
      (r : ℕ), 3 * r = S.Y.card ∧
      Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' ∅ ∧
      HasDecomp p F (S.Y.image fun e => pos' (.inl e)) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 27 * S.Y.card ∧
      Z ⊆ Z' ∧ Z'.card ≤ Z.card + 2 * S.Y.card ∧
      PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos') (9 * r) ∧
      ∀ W m, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W m →
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (9 * r + m) := by
  obtain ⟨Ts, hv, hp, hc, hn⟩ := exists_partition p S.Y F hcard c hvec
  have hnr : (3 : ℝ) * Ts.length = S.Y.card := by exact_mod_cast hn
  obtain ⟨pos', U', Z', ph', bd', dec, _, _, hu, huc, hz, hzc, tr, cont⟩ :=
    cut_partition a d hF hs hB hd Ts ph bd hv hp hc (by linarith)
  refine ⟨pos', U', Z', Ts.length, hn, ph', bd', dec, hu, ?_, hz, ?_, tr, cont⟩
  · omega
  · omega

/-- Use the exact integer max(c,0) vector retained by physical padding. -/
theorem cut_from_padded_coefficients {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {G : SimpleGraph V} [DecidableRel G.Adj] {B : Finset (Sym2 V)} (a d : ℝ)
    (hF : ThreeStepLinks F) (hcard : ∀ τ ∈ F, τ.card = 3)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (hB : DegBounded B d) (hd : 0 ≤ d) {S : Data V}
    {pos : Tok V → Sym2 V} {U : Finset (Sym2 V)} {Z : Finset V}
    (ph : Phys p F G B S.tokens pos U Z) (bd : Bdry p F S pos S.Y)
    (c : Multiset (Fin t) → ℤ)
    (hvec : edgeVec p S.Y = ∑ τ ∈ F, max (c τ) 0 • typeEdgeVec τ)
    (hb : (Z.card : ℝ) + 4 * (d + U.card) + 110 * S.Y.card < a) :
    ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V)
      (r : ℕ), 3 * r = S.Y.card ∧
      Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' ∅ ∧
      HasDecomp p F (S.Y.image fun e => pos' (.inl e)) ∧
      U ⊆ U' ∧ U'.card ≤ U.card + 27 * S.Y.card ∧
      Z ⊆ Z' ∧ Z'.card ≤ Z.card + 2 * S.Y.card ∧
      PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) (S.tokens.image pos') (9 * r) ∧
      ∀ W m, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W m →
        PhysicalMoves p F G.edgeFinset B U (S.tokens.image pos) W (9 * r + m) :=
  cut_from_coefficients a d hF hcard hs hB hd ph bd _
    (PositiveTargetBridgeStage96.natural_positive_vector p S.Y F c hvec) hb

/-- Scalar padding overhead for the full deployment, insertion and cut. -/
theorem padded_cut_budget {z u zp up x d a k q : ℝ}
    (hx : x ≤ k + 3 * q) (hu : up ≤ u + 3 * q) (hz : zp ≤ z + 6 * q)
    (hb : z + 272 * k + 834 * q + 4 * (d + u) < a) :
    zp + 272 * x + 4 * (d + up) < a := by
  linarith

/-- Deployment, insertion and all original cuts, retaining the catalyst frame
needed by cleanup. The target partition is produced from the coefficients. -/
theorem selected_cut_producer {p : V → Fin t} {F : Finset (Multiset (Fin t))}
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
      S.cats ⊆ G.edgeFinset ∧ Disjoint S.cats B ∧ S.cats.card ≤ 3 * X.card ∧
      Phys p F G B S.tokens pos U' Z' ∧ Bdry p F S pos ∅ ∧
      HasDecomp p F (S.Y.image fun e => pos (.inl e)) ∧
      U'.card ≤ U.card + 66 * X.card ∧ Z'.card ≤ Z.card + 8 * X.card ∧ n ≤ 7 * X.card ∧
      PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) (S.tokens.image pos) n ∧
      ∀ W k, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos) W k →
        PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) W (n + k) := by
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  obtain ⟨S, L, m, cz, cz', U₂, Z₂, hm, _, _, _, hYc, hYvec, _, hAc, _, _, hLc, _,
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
  obtain ⟨pos', U', Z', r, hr, ph, bd, dec, _, hUc, _, hZc, tr, cont⟩ :=
    cut_from_coefficients a d hF hcard hs hB hd (initial_phys fr inv) (initial_bdry fr inv)
      c (hYvec.trans hvec) (by rw [hYr]; linarith)
  have cfg := S.config_eq_image cz cz' S.A
  refine ⟨S, _, pos', U', Z', m + 3 * S.A.card + 9 * r,
    hYc, hAX, fr, hdec, hDG, hDBL.mono_right subset_union_left, ?_, ph, bd, dec,
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

end PartitionedTriangleAbsorption.SelectedTripleCutStage98
