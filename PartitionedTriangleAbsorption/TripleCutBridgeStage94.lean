/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TripleCutInductionStage94

/-! # From the accepted insertion return to the triple cuts

`initial_phys` and `initial_bdry` show that the final state of the accepted
catalyst insertion (`TypedCatalystBridgeStage93.catalyst_producer`) is a
physical token state satisfying the boundary invariant with all original
tokens remaining. The active set used for the cuts is the insertion's
forbidden set `Z₀` together with all carriers. The proof uses the accepted
incidence identities `tokAt_cz`, `tokAt_cz'`, `tokAt_cs`, `tokAt_ct`,
`tokAt_other`, `tokPos_injOn`, the carrier labels and
`original_token_type`; no new distinctness hypothesis is supplied.

`triple_cut_producer` composes deployment, catalyst selection, insertion and
the cut of an arbitrary given disjoint family of valid target triples of the
deployed original tokens into one physical trace, with explicit budget
`|Z| + 272 |X| + 4 (d + |U|) < a`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TripleCutStage94

open Finset AntiEdgeSelection TypedTransformer CatalystSelectionStage89
  CatalystInsertionStage89 PhysicalMovesStage86

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- The empty edge set decomposes. -/
theorem hasDecomp_empty {p : V → Fin t} {F : Finset (Multiset (Fin t))} :
    HasDecomp p F (∅ : Finset (Sym2 V)) :=
  ⟨∅, fun _ h => absurd h (notMem_empty _), by simp, by simp⟩

theorem toks_subset_allToks {T : TargetTriple V t} {Ts : List (TargetTriple V t)}
    (hT : T ∈ Ts) : T.toks ⊆ allToks Ts := by
  induction Ts with
  | nil => simp at hT
  | cons T' Ts ih =>
    rw [allToks_cons]
    rcases List.mem_cons.mp hT with rfl | h
    · exact subset_union_left
    · exact (ih h).trans subset_union_right

/-- Distinct tokens: a disjoint family of `r` valid triples has `3 r` tokens. -/
theorem card_allToks {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    {Ts : List (TargetTriple V t)} (hval : ∀ T ∈ Ts, T.Valid p F)
    (hpw : Ts.Pairwise (fun T T' => Disjoint T.toks T'.toks)) :
    (allToks Ts).card = 3 * Ts.length := by
  induction Ts with
  | nil => simp
  | cons T Ts ih =>
    rw [List.pairwise_cons] at hpw
    obtain ⟨n12, n13, n23, -, -, -, -⟩ := hval T (List.mem_cons_self ..)
    have hT : T.toks.card = 3 := by
      rw [TargetTriple.toks, card_insert_of_notMem (by simp [n12, n13]), card_pair n23]
    rw [allToks_cons, card_union_of_disjoint (disjoint_allToks hpw.1), hT,
      ih (fun T' h => hval T' (List.mem_cons_of_mem _ h)) hpw.2, List.length_cons]
    ring

/-- **The boundary invariant with nothing cut yet**: all original tokens. -/
theorem Bdry.all_done {p : V → Fin t} {F : Finset (Multiset (Fin t))} {S : Data V}
    {pos : Tok V → Sym2 V} (bd : Bdry p F S pos ∅) :
    HasDecomp p F (S.Y.image fun e => pos (.inl e)) ∧
    ∀ v, tokAtP S pos v = ∅ ∨
      (∃ κ κ' : V × Fin 3, κ ≠ κ' ∧ tokAtP S pos v = {.inr κ, .inr κ'}) ∨
      (∃ e e', e ∈ S.Y ∧ e' ∈ S.Y ∧ e ≠ e' ∧ tokAtP S pos v = {.inl e, .inl e'}) := by
  refine ⟨by simpa using bd.done_decomp, fun v => ?_⟩
  simpa using bd.other v (by simp)

variable [Fintype V]

section initial

variable {p : V → Fin t} {F : Finset (Multiset (Fin t))} {G : SimpleGraph V}
  [DecidableRel G.Adj] {B : Finset (Sym2 V)} {S : Data V} {Z₀ : Finset V} {cz cz' : V → V}
  {U : Finset (Sym2 V)} {Z : Finset V}

/-- Every vertex carrying a token is a carrier or a catalytic vertex. -/
theorem mem_carriers_or_catalytic (fr : Frame p F G B S Z₀) {q : Tok V} (hq : q ∈ S.tokens)
    {v : V} (hv : v ∈ S.tokPos cz cz' S.A q) : v ∈ S.carriers cz cz' ∪ S.catalytic := by
  by_contra h
  have hm : q ∈ S.tokAt cz cz' S.A v := mem_filter.mpr ⟨hq, hv⟩
  rw [tokAt_other fr h] at hm
  exact notMem_empty _ hm

/-- The insertion's final state is a physical token state for the active set
`Z₀ ∪ carriers`. -/
theorem initial_phys (fr : Frame p F G B S Z₀)
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z) :
    Phys p F G B S.tokens (S.tokPos cz cz' S.A) U (Z₀ ∪ S.carriers cz cz') := by
  have hcfg := S.config_eq_image cz cz' S.A
  refine ⟨tokPos_injOn fr inv.carriers, hcfg ▸ inv.hist, hcfg ▸ inv.real, hcfg ▸ inv.forb,
    ?_, ?_⟩
  · intro q hq v hv
    rcases mem_union.mp (mem_carriers_or_catalytic fr hq hv) with h | h
    · exact mem_union_right _ h
    · apply mem_union_left
      simp only [Data.catalytic, mem_union, mem_image] at h
      rcases h with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact (fr.mem_cat hy).2.1
      · exact (fr.mem_cat hy).2.2
  · intro q hq u v huv
    exact inv.links u v (hcfg ▸ mem_image.mpr ⟨q, hq, huv⟩)

omit [Fintype V] in
/-- Size of the active set used for the cuts. -/
theorem carriers_card_le : (S.carriers cz cz').card ≤ 2 * S.A.card := by
  unfold Data.carriers
  have h1 := card_union_le (S.A.image cz) (S.A.image cz')
  have h2 := card_image_le (s := S.A) (f := cz)
  have h3 := card_image_le (s := S.A) (f := cz')
  omega

/-- **Initial boundary invariant**: the insertion's final state, with every
original token remaining. -/
theorem initial_bdry (fr : Frame p F G B S Z₀)
    (inv : Inv p F G B S Z₀ cz cz' S.A U Z) :
    Bdry p F S (S.tokPos cz cz' S.A) S.Y := by
  have hc := inv.carriers
  refine ⟨Subset.refl _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e _
    exact TypedCatalystBridgeStage93.original_token_type inv e
  · intro e he v hv
    obtain ⟨u, hu, h | h⟩ := curY_carrier fr he hv
    · subst h
      have he' : e = s(u, S.nm u) := (cz_mem_curY fr hc hu he).mp hv
      refine ⟨u, hu, 0, by decide, ?_, ?_⟩
      · rw [catV_zero]; exact (catTok_full hu).1
      · rw [he']; exact tokAt_cz fr hc hu
    · subst h
      have he' : e = s(u, S.np u) := (cz'_mem_curY fr hc hu he).mp hv
      refine ⟨u, hu, 1, by decide, ?_, ?_⟩
      · rw [catV_one]; exact (catTok_full hu).2.1
      · rw [he']; exact tokAt_cz' fr hc hu
  · intro y hy; exact tokAt_cs fr hc hy
  · intro y hy; exact tokAt_ct fr hc hy
  · intro y hy i hi
    have hi' : i = 0 ∨ i = 1 := by fin_cases i <;> simp_all
    rcases hi' with rfl | rfl
    · exact ⟨cz y, by rw [catV_zero]; exact (catTok_full hy).1, (inv.carrier_label y hy).1⟩
    · exact ⟨cz' y, by rw [catV_one]; exact (catTok_full hy).2.1, (inv.carrier_label y hy).2⟩
  · intro y hy; exact (catTok_full hy).2.2
  · intro v hv
    by_cases hK : v ∈ S.carriers cz cz'
    · exfalso
      simp only [Data.carriers, mem_union, mem_image] at hK
      rcases hK with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact hv _ (fr.nm_mem hy).1 ((cz_mem_curY fr hc hy (fr.nm_mem hy).1).mpr rfl)
      · exact hv _ (fr.nm_mem hy).2 ((cz'_mem_curY fr hc hy (fr.nm_mem hy).2).mpr rfl)
    by_cases hC : v ∈ S.catalytic
    · right; left
      simp only [Data.catalytic, mem_union, mem_image] at hC
      rcases hC with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact ⟨(y, 0), (y, 2), by simp, tokAt_cs fr hc hy⟩
      · exact ⟨(y, 1), (y, 2), by simp, tokAt_ct fr hc hy⟩
    · left
      exact tokAt_other fr (by simp [hK, hC])
  · intro e he; simp at he
  · simpa using hasDecomp_empty

end initial

/-- **End-to-end producer: deployment, catalysts, insertion and the cut of a
given family of target triples.** The family is arbitrary combinatorial data
(valid, pairwise disjoint, consisting of deployed original tokens); it is
quantified after the deployment, since it refers to the deployed tokens. -/
theorem triple_cut_producer {p : V → Fin t} {F : Finset (Multiset (Fin t))}
    (G : SimpleGraph V) [DecidableRel G.Adj] (a d : ℝ) (hF : ThreeStepLinks F)
    (hs : PairMoveSelectionStage85.CompatibleSupply p F G a)
    (B U X : Finset (Sym2 V)) (Z : Finset V)
    (hB : DegBounded B d) (hd : 0 ≤ d)
    (hXU : X ⊆ U) (hXG : X ⊆ G.edgeFinset) (hXB : Disjoint X B)
    (hZ : ∀ e ∈ X, ∀ v ∈ e, v ∈ Z)
    (hact : ∀ u v, s(u, v) ∈ X → ∃ k, Link F (p u) (p v) k)
    (heven : ∀ v, Even (incidentLoad X v))
    (hb : (Z.card : ℝ) + 272 * X.card + 4 * (d + U.card) < a) :
    ∃ (S : Data V) (cz cz' : V → V) (U₂ : Finset (Sym2 V)) (m : ℕ),
      S.Y.card = X.card ∧ edgeVec p S.Y = edgeVec p X ∧ S.Y ⊆ G.edgeFinset ∧
      Disjoint S.Y B ∧ HasDecomp p F S.cats ∧ S.cats ⊆ G.edgeFinset ∧
      Disjoint S.cats B ∧ m ≤ X.card ∧
      U₂.card ≤ U.card + 39 * X.card ∧
      PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats)
        (S.tokens.image (S.tokPos cz cz' S.A)) (m + 3 * S.A.card) ∧
      Bdry p F S (S.tokPos cz cz' S.A) S.Y ∧
      ∀ Ts : List (TargetTriple V t), (∀ T ∈ Ts, T.Valid p F) →
        Ts.Pairwise (fun T T' => Disjoint T.toks T'.toks) → allToks Ts ⊆ S.Y →
        ∃ (pos' : Tok V → Sym2 V) (U' : Finset (Sym2 V)) (Z' : Finset V),
          Phys p F G B S.tokens pos' U' Z' ∧ Bdry p F S pos' (S.Y \ allToks Ts) ∧
          (∀ T ∈ Ts, ∃ zA zB zC : V,
            TriangleCut p F S pos' T.e₁ T.e₂ T.e₃ T.i T.j T.k zA zB zC) ∧
          (∀ e, e ∉ allToks Ts → pos' (.inl e) = S.tokPos cz cz' S.A (.inl e)) ∧
          (∀ y, pos' (.inr (y, 2)) = S.tokPos cz cz' S.A (.inr (y, 2))) ∧
          U₂ ⊆ U' ∧ U'.card ≤ U₂.card + 81 * Ts.length ∧
          PhysicalMoves p F G.edgeFinset B U₂ (S.tokens.image (S.tokPos cz cz' S.A))
            (S.tokens.image pos') (9 * Ts.length) ∧
          PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) (S.tokens.image pos')
            (m + 3 * S.A.card + 9 * Ts.length) ∧
          ∀ W k, PhysicalMoves p F G.edgeFinset B U' (S.tokens.image pos') W k →
            PhysicalMoves p F G.edgeFinset B (U ∪ S.cats) (X ∪ S.cats) W
              (m + 3 * S.A.card + 9 * Ts.length + k) := by
  have hX0 : (0 : ℝ) ≤ X.card := Nat.cast_nonneg _
  obtain ⟨S, L, m, cz, cz', U₂, Z₂, hm, -, hYG, hYB, hYc, hYvec, hA, hAc, hUL, -, hLc, -,
      hdec, hDG, hDBL, hDc, fr, inv, hU₂, htr, hcont, -⟩ :=
    TypedCatalystBridgeStage93.catalyst_producer G a d hF hs B U X Z hB hd hXU hXG hXB hZ hact
      heven (by linarith)
  have hcfg := S.config_eq_image cz cz' S.A
  have hAX : S.A.card = X.card := hAc.trans hYc
  have hU₂c : U₂.card ≤ U.card + 39 * X.card := by
    have h1 : (L ∪ S.cats).card ≤ L.card + S.cats.card := card_union_le _ _
    omega
  have hZcut : (Z ∪ S.A ∪ catVertsAll S.A S.co S.cs S.ct ∪ S.carriers cz cz').card ≤
      Z.card + 6 * X.card := by
    have h1 := card_union_le (Z ∪ S.A ∪ catVertsAll S.A S.co S.cs S.ct) (S.carriers cz cz')
    have h2 := card_union_le (Z ∪ S.A) (catVertsAll S.A S.co S.cs S.ct)
    have h3 := card_union_le Z S.A
    have h4 := catVertsAll_card_le S.A S.co S.cs S.ct
    have h5 := carriers_card_le (S := S) (cz := cz) (cz' := cz')
    omega
  have ph₀ := initial_phys fr inv
  have bd₀ := initial_bdry fr inv
  refine ⟨S, cz, cz', U₂, m, hYc, hYvec, hYG, hYB, hdec, hDG,
    hDBL.mono_right subset_union_left, hm, hU₂c, hcfg ▸ htr, bd₀, ?_⟩
  intro Ts hval hpw hsub
  have hlen : 3 * Ts.length ≤ X.card := by
    rw [← card_allToks hval hpw, ← hYc]
    exact card_le_card hsub
  have hlenr : (3 : ℝ) * Ts.length ≤ X.card := by exact_mod_cast hlen
  have hZr : ((Z ∪ S.A ∪ catVertsAll S.A S.co S.cs S.ct ∪ S.carriers cz cz').card : ℝ) ≤
      Z.card + 6 * X.card := by
    exact_mod_cast hZcut
  have hUr : (U₂.card : ℝ) ≤ U.card + 39 * X.card := by exact_mod_cast hU₂c
  obtain ⟨pos', U', Z', ph', bd', tris, unO, un2, -, -, -, hUU', hU', htr', hcont'⟩ :=
    cut_all a d hF hs hB hd Ts _ S.Y U₂ _ ph₀ bd₀
      (fun T hT => ⟨hval T hT, (toks_subset_allToks hT).trans hsub⟩)
      hpw (by linarith)
  refine ⟨pos', U', Z', ph', bd', tris, unO, un2, hUU', hU', htr', ?_, ?_⟩
  · have h := hcont _ _ (hcfg ▸ htr')
    rwa [show m + (3 * S.A.card + 9 * Ts.length) = m + 3 * S.A.card + 9 * Ts.length
      by ring] at h
  · intro W k hW
    have h := hcont _ _ (hcfg ▸ hcont' W k hW)
    rwa [show m + (3 * S.A.card + (9 * Ts.length + k)) = m + 3 * S.A.card + 9 * Ts.length + k
      by ring] at h

end PartitionedTriangleAbsorption.TripleCutStage94
