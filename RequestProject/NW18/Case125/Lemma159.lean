/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case125.Claim1594

@[expose] public section

/-!
# Lemma 15.9 (many oddballs cleaning lemma), case `E = ∅`

This is the cleaning step of the proof of Theorem 12.5 (§15.2–15.3 of the paper).
`lemma_15_9` is proved here from Claims 15.9.1, 15.9.2 (`Surplus.lean`), 15.9.3
(`Packing158.lean`), the counting lemmas of `Cleaning.lean`, and **Claim 15.9.4**
(`claim_15_9_4`, proved in `Claim1594.lean`): it is the step that decomposes all oddballs one
at a time with the One Oddball Cleaning Lemma 15.7 (`oddball_step` in `OddballStep.lean`).  The
paper uses Pósa's theorem for the perfect matching of the link; here the link is paired by a
pairing inside its larger side followed by a dense bipartite matching (Hall's theorem),
`link_pairing` in `LinkPairing.lean`.  Claim 15.9.5 is the elementary choice of
`IntSurplus/6` triangles of `T'` done inside the proof of `lemma_15_9`.

Formalization choices (all documented deviations are in the direction of the paper's proof):
* only the case `E = ∅` of the paper's lemma is stated (this is the case used for
  Theorem 12.5; the version with a set `E` of at most two edges, used in cases (3)–(4), is not
  stated here);
* the minimum degree hypothesis is `δ(G) ≥ 3n/4` (as in Theorem 12.5, where the lemma is
  applied) instead of the paper's `δ(G) ≥ (3/4 − γ) n`.  With `(3/4 − γ) n` the statement is
  false: e.g. `V₁, V₂` of size `n/2`, complete between them, each `G[V_i]` an
  `(n/4 − 2)`-regular graph containing many edge-disjoint triangles (`24 ∣ n`) is
  triangle-divisible, `γ`-extremal and `γ`-cross-balanced with `δ = 3n/4 − 2 ≥ (3/4 − γ) n`,
  `B = ∅`, but `IntSurplus(G) = 2e(G) − 3e₁₂(G) = −n < 0`; since removing a triangle changes
  `IntSurplus` by `0` (cross) or `6` (interior), no residual of a triangle packing is
  cross-divisible.  (The paper's Claim 15.9.2 uses `δ(G) ≥ 3n/4`.)
* the reserve `T₀` is assumed to avoid `A` (Claim 12.5.1 provides a reserve in `G \ A`);
* the conclusion additionally records that the packing `T` uses at most `3 √γ n²` edges not
  incident with `A`.  In the paper's proof `T = T₁ ∪ T₂`, where every triangle of `T₁` meets `A`
  (so `T₁` has at most `|A| n / 2 ≤ √γ n²` triangles, each with at most one edge outside `A`),
  and `T₂ ⊆ T₀` consists of `IntSurplus / 6 ≤ γ n² / 3` interior triangles (Claim 15.9.1).
  This bound is needed to transfer hypothesis (c) of Theorem 14.6 to the cleaned graph.

The cleaned graph `G' = (G − E(T)) \ A` is described through its edge set
`R = E(G) ∖ ⋃ T` (which avoids `A`, since `T` saturates `A`).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

/-- **Claim 15.9.4**.  Let `G` be as in Lemma 15.9 and let `T'` be a packing
of interior triangles avoiding `A` whose edge set has maximum degree at most `√γ n`.  Then there
is a triangle packing `T₁` of `G − E(T')` all of whose triangles meet `A`, which covers every
edge of `G` incident with `A`, and which uses at most `0.01 n |B|` interior triangles,
`B = {v : IntDeg(v) ≥ 0.371 n}`.

In the paper this is proved by enumerating `A = {v₁, …, v_k}` and applying the One Oddball
Cleaning Lemma 15.7 to `v_i` in `(G − E(T') − E(T₁^{(i-1)})) ∖ {v₁, …, v_{i-1}}`; Lemma 15.7
produces the triangles at `v_i` from a perfect matching of a suitable subgraph of `G[N(v_i)]`
given by Pósa's theorem.  The formal proof (`claim_15_9_4_proof`) follows this scheme, with the
perfect matching obtained from `link_pairing` instead of Pósa's theorem.  (The hypothesis
`B ⊆ A` turns out not to be needed for this claim.) -/
theorem claim_15_9_4 :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 2) (T' : Finset (Finset V)) (A : Finset V),
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
        IsTwoExtremal γ G p → IsCrossBalanced γ G p →
        IsTrianglePacking G T' → (∀ s ∈ T', IsInteriorTri p s) →
        (∀ s ∈ T', ∀ x ∈ s, x ∉ A) →
        (∀ v, (((T'.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ) ≤
          Real.sqrt γ * Fintype.card V) →
        (∀ v, 0.371 * (Fintype.card V : ℝ) ≤ (partDeg G p v (p v) : ℝ) → v ∈ A) →
        (A.card : ℝ) ≤ 2 * Real.sqrt γ * Fintype.card V →
        ∃ T₁ : Finset (Finset V), IsTrianglePacking G T₁ ∧
          Disjoint (T₁.biUnion triEdges) (T'.biUnion triEdges) ∧
          (∀ t ∈ T₁, ∃ a ∈ t, a ∈ A) ∧
          (∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ T₁.biUnion triEdges) ∧
          ((T₁.filter (fun t => IsInteriorTri p t)).card : ℝ) ≤
            0.01 * (Fintype.card V : ℝ) *
              ((univ.filter (fun v => 0.371 * (Fintype.card V : ℝ) ≤
                (partDeg G p v (p v) : ℝ))).card : ℝ) :=
  claim_15_9_4_proof

/-- **Lemma 15.9 (Many Oddballs Cleaning Lemma), case `E = ∅`**, proved from
Claim 15.9.4.
For all sufficiently small `γ > 0` and large `n`: let `G` be a triangle-divisible graph on `n`
vertices with a bipartition `p`, `δ(G) ≥ 3n/4`, `γ`-extremal and `γ`-cross-balanced,
containing a packing `T₀` of at least `2 √γ n²` interior triangles avoiding `A`, where
`A ⊇ B = {v : IntDeg(v) ≥ 0.371 n}` and `|A| ≤ 2 √γ n`.  Then there is a triangle packing `T`
of `G` saturating `A` such that `R = E(G) ∖ ⋃ T` is cross-divisible (`IntSurplus = 0`), every
vertex outside `A` has `R`-degree at least `(3/4 − 7 √γ)(n − |A|)`, and `T` has at most
`3 √γ n²` edges not incident with `A`. -/
theorem lemma_15_9 :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 2) (T₀ : Finset (Finset V)) (A : Finset V),
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
        IsTwoExtremal γ G p → IsCrossBalanced γ G p →
        IsTrianglePacking G T₀ → (∀ s ∈ T₀, ∃ i, ∀ x ∈ s, p x = i) →
        (∀ s ∈ T₀, ∀ x ∈ s, x ∉ A) →
        2 * Real.sqrt γ * (Fintype.card V : ℝ) ^ 2 ≤ (T₀.card : ℝ) →
        (∀ v, 0.371 * (Fintype.card V : ℝ) ≤ (partDeg G p v (p v) : ℝ) → v ∈ A) →
        (A.card : ℝ) ≤ 2 * Real.sqrt γ * Fintype.card V →
        ∃ T : Finset (Finset V), IsTrianglePacking G T ∧
          (∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∈ T.biUnion triEdges) ∧
          intSurplus p (G.edgeFinset \ T.biUnion triEdges) = 0 ∧
          (∀ v, v ∉ A → (3 / 4 - 7 * Real.sqrt γ) * ((Fintype.card V : ℝ) - A.card) ≤
            (((G.edgeFinset \ T.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ)) ∧
          (((T.biUnion triEdges).filter (fun e => ∀ x ∈ e, x ∉ A)).card : ℝ) ≤
            3 * Real.sqrt γ * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨γ₁, hγ₁, h1594⟩ := claim_15_9_4
  refine ⟨min γ₁ (1 / 10000), lt_min hγ₁ (by norm_num), fun γ hγ hγ₀ => ?_⟩
  have hγ1 : γ ≤ γ₁ := hγ₀.trans (min_le_left _ _)
  have hγ2 : γ ≤ 1 / 10000 := hγ₀.trans (min_le_right _ _)
  obtain ⟨n₁, hn₁⟩ := h1594 γ hγ hγ1
  set r := Real.sqrt γ with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hγ
  have hr1 : r ≤ 1 / 100 := by
    have : r ≤ Real.sqrt ((1 / 100) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hrr : r * r = γ := Real.mul_self_sqrt hγ.le
  refine ⟨max n₁ (⌈20 / r⌉₊ + 1), fun V _ _ G _ p T₀ A hn hdiv hδ hext hbal hT₀ hT₀int hT₀A
    hT₀card hB hA => ?_⟩
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hn20 : 20 ≤ r * n := by
    have h1 : ((⌈20 / r⌉₊ + 1 : ℕ) : ℝ) ≤ n := by
      rw [hndef]; exact_mod_cast le_trans (le_max_right _ _) hn
    have h2 := Nat.le_ceil (20 / r)
    push_cast at h1
    have : 20 / r ≤ n := by linarith
    rw [div_le_iff₀ hr0] at this; linarith
  obtain ⟨-, hcl, -⟩ := lemma_15_6 hγ (by linarith) G p hδ hext
  -- Claim 15.9.3: a low-degree subpacking `T'` of the reserve
  obtain ⟨T', hT'T₀, hT'card, hT'deg⟩ := claim_15_9_3 G hT₀ hγ (by linarith) hn20 hT₀card
  have hT'pack : IsTrianglePacking G T' :=
    ⟨fun t ht => hT₀.1 t (hT'T₀ ht), hT₀.2.subset (by exact_mod_cast hT'T₀)⟩
  have hT'int : ∀ s ∈ T', IsInteriorTri p s := fun s hs => hT₀int s (hT'T₀ hs)
  have hT'A : ∀ s ∈ T', ∀ x ∈ s, x ∉ A := fun s hs => hT₀A s (hT'T₀ hs)
  -- Claim 15.9.4: decomposing the oddballs
  obtain ⟨T₁, hT₁, hdisj, hmeet, hcov, hint1⟩ := hn₁ V G p T' A
    (le_trans (le_max_left _ _) hn) hdiv hδ hext hbal hT'pack hT'int hT'A hT'deg hB hA
  set C₁ := T₁.biUnion triEdges with hC₁def
  set C' := T'.biUnion triEdges with hC'def
  have hC₁E : C₁ ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT₁.1 t ht)
  have hC'E : C' ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT'pack.1 t ht)
  -- surplus bookkeeping (Claims 15.9.1, 15.9.2 and Proposition 15.2)
  have hIS1 := claim_15_9_1 G p hγ.le hext
  have hIS2 := claim_15_9_2 G p (r := r) (by linarith) hδ hcl
  have h6 := six_dvd_intSurplus G p hdiv
  have hC₁IS := intSurplus_biUnion p T₁ (fun t ht => (hT₁.1 t ht).card_eq) hT₁.2
  set k₁ := (T₁.filter (fun t => IsInteriorTri p t)).card with hk₁
  have hE1 : intSurplus p (G.edgeFinset \ C₁) = intSurplus p G.edgeFinset - 6 * k₁ := by
    rw [intSurplus_sdiff p hC₁E, hC₁IS]
  have hE1nn : 0 ≤ intSurplus p (G.edgeFinset \ C₁) := by
    have : (6 * k₁ : ℝ) ≤ (intSurplus p G.edgeFinset : ℝ) := by linarith
    have : ((6 * k₁ : ℤ) : ℝ) ≤ (intSurplus p G.edgeFinset : ℝ) := by push_cast; linarith
    have : (6 * k₁ : ℤ) ≤ intSurplus p G.edgeFinset := by exact_mod_cast this
    rw [hE1]; linarith
  have hE1dvd : (6 : ℤ) ∣ intSurplus p (G.edgeFinset \ C₁) := by
    rw [hE1]; exact dvd_sub h6 (dvd_mul_right 6 _)
  obtain ⟨c, hc⟩ := hE1dvd
  have hc0 : 0 ≤ c := by linarith
  set m := c.toNat with hmdef
  have hcm : (m : ℤ) = c := Int.toNat_of_nonneg hc0
  have hmle : (m : ℝ) ≤ γ * n ^ 2 / 2 := by
    have h1 : (6 * c : ℝ) ≤ (intSurplus p G.edgeFinset : ℝ) := by
      have : (6 * c : ℤ) ≤ intSurplus p G.edgeFinset := by
        rw [← hc, hE1]; have : (0 : ℤ) ≤ k₁ := Nat.cast_nonneg _; linarith
      exact_mod_cast this
    have h2 : (m : ℝ) = c := by exact_mod_cast hcm
    rw [h2]; linarith
  have hmT' : m ≤ T'.card := by
    have : (m : ℝ) ≤ T'.card := hmle.trans hT'card
    exact_mod_cast this
  -- Claim 15.9.5: `IntSurplus / 6` interior triangles of `T'`
  obtain ⟨T₂, hT₂T', hT₂card⟩ := exists_subset_card_eq hmT'
  set C₂ := T₂.biUnion triEdges with hC₂def
  have hC₂C' : C₂ ⊆ C' := biUnion_subset_biUnion_of_subset_left _ hT₂T'
  have hT₂pack : IsTrianglePacking G T₂ :=
    ⟨fun t ht => hT'pack.1 t (hT₂T' ht), hT'pack.2.subset (by exact_mod_cast hT₂T')⟩
  have hC₂IS := intSurplus_biUnion p T₂ (fun t ht => (hT₂pack.1 t ht).card_eq) hT₂pack.2
  rw [filter_true_of_mem fun t ht => hT'int t (hT₂T' ht), hT₂card] at hC₂IS
  have hunion : (T₁ ∪ T₂).biUnion triEdges = C₁ ∪ C₂ := union_biUnion
  refine ⟨T₁ ∪ T₂, ⟨fun s hs => ?_, ?_⟩, fun u v huv huA => ?_, ?_, fun v hv => ?_, ?_⟩
  · rcases mem_union.mp hs with h | h
    · exact hT₁.1 s h
    · exact hT₂pack.1 s h
  · rw [coe_union, Set.pairwiseDisjoint_union]
    refine ⟨hT₁.2, hT₂pack.2, fun i hi j hj _ => ?_⟩
    exact hdisj.mono (subset_biUnion_of_mem _ hi) (subset_biUnion_of_mem _ (hT₂T' hj))
  · rw [hunion]; exact mem_union_left _ (hcov u v huv huA)
  · -- cross-divisibility
    have hsd : G.edgeFinset \ (C₁ ∪ C₂) = (G.edgeFinset \ C₁) \ C₂ := by
      ext e; simp only [mem_sdiff, mem_union, not_or, and_assoc]
    rw [hunion, hsd]
    have hC₂sub : C₂ ⊆ G.edgeFinset \ C₁ := by
      intro e he
      refine mem_sdiff.mpr ⟨hC'E (hC₂C' he), fun h => ?_⟩
      exact disjoint_left.mp hdisj h (hC₂C' he)
    rw [intSurplus_sdiff p hC₂sub, hC₂IS, hc, ← hcm]
    ring
  · -- minimum degree of the residual
    have hcover : G.edgeFinset.filter (fun e => v ∈ e) ⊆
        ((G.edgeFinset \ (T₁ ∪ T₂).biUnion triEdges).filter (fun e => v ∈ e) ∪
          C₁.filter (fun e => v ∈ e)) ∪ C₂.filter (fun e => v ∈ e) := by
      intro e he
      rw [mem_filter] at he
      rw [hunion]
      simp only [mem_union, mem_filter, mem_sdiff]
      by_cases h1 : e ∈ C₁
      · exact Or.inl (Or.inr ⟨h1, he.2⟩)
      · by_cases h2 : e ∈ C₂
        · exact Or.inr ⟨h2, he.2⟩
        · exact Or.inl (Or.inl ⟨⟨he.1, by tauto⟩, he.2⟩)
    have hc1 := (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
    rw [card_edgeFinset_filter_mem] at hc1
    have hC₁v : (C₁.filter (fun e => v ∈ e)).card ≤ 2 * A.card :=
      (card_filter_edges_mem_le G hT₁ v).trans
        (Nat.mul_le_mul_left 2 (card_filter_mem_le_of_meets G hT₁ hmeet hv))
    have hC₂v : ((C₂.filter (fun e => v ∈ e)).card : ℝ) ≤ r * n := by
      have : (C₂.filter (fun e => v ∈ e)).card ≤ (C'.filter (fun e => v ∈ e)).card :=
        card_le_card (filter_subset_filter _ hC₂C')
      exact le_trans (by exact_mod_cast this) (hT'deg v)
    have hdeg : 3 / 4 * n ≤ (G.degree v : ℝ) := by
      have h1 := G.minDegree_le_degree v
      have : (3 : ℝ) * n ≤ 4 * G.minDegree := by rw [hndef]; exact_mod_cast hδ
      have : (G.minDegree : ℝ) ≤ G.degree v := by exact_mod_cast h1
      linarith
    have hc1R : (G.degree v : ℝ) ≤
        ((G.edgeFinset \ (T₁ ∪ T₂).biUnion triEdges).filter (fun e => v ∈ e)).card +
          (C₁.filter (fun e => v ∈ e)).card + (C₂.filter (fun e => v ∈ e)).card := by
      exact_mod_cast hc1
    have hC₁vR : ((C₁.filter (fun e => v ∈ e)).card : ℝ) ≤ 2 * A.card := by
      exact_mod_cast hC₁v
    have hA0 : (0 : ℝ) ≤ A.card := Nat.cast_nonneg _
    have hrA : r * A.card ≤ r * (2 * r * n) := mul_le_mul_of_nonneg_left hA hr0.le
    have hrn : r * r * n ≤ 1 / 100 * r * n := by
      have := mul_le_mul_of_nonneg_right hr1 (mul_nonneg hr0.le hn0)
      linarith
    have hrn0 : 0 ≤ r * n := mul_nonneg hr0.le hn0
    linarith
  · -- few edges avoiding `A`
    rw [hunion]
    have hsub : (C₁ ∪ C₂).filter (fun e => ∀ x ∈ e, x ∉ A) ⊆
        C₁.filter (fun e => ∀ x ∈ e, x ∉ A) ∪ C₂ := by
      intro e he
      simp only [mem_filter, mem_union] at he ⊢
      tauto
    have h1 := (card_le_card hsub).trans (card_union_le _ _)
    have h2 : (C₁.filter (fun e => ∀ x ∈ e, x ∉ A)).card ≤ T₁.card :=
      card_offA_le_of_meets G hT₁ hmeet
    have h3 := two_mul_card_le_of_meets G hT₁ hmeet
    have h4 : C₂.card ≤ 6 * m := by
      have := card_biUnion_triEdges_le G T₂ hT₂pack.1
      rw [hT₂card] at this; exact this
    have h1R : (((C₁ ∪ C₂).filter (fun e => ∀ x ∈ e, x ∉ A)).card : ℝ) ≤
        T₁.card + 6 * m := by
      have : ((C₁ ∪ C₂).filter (fun e => ∀ x ∈ e, x ∉ A)).card ≤ T₁.card + 6 * m := by
        omega
      exact_mod_cast this
    have h3R : 2 * (T₁.card : ℝ) ≤ A.card * n := by rw [hndef]; exact_mod_cast h3
    have hAn : (A.card : ℝ) * n ≤ 2 * r * n * n := mul_le_mul_of_nonneg_right hA hn0
    have hγn : γ * n ^ 2 ≤ 1 / 100 * r * n ^ 2 := by
      rw [← hrr]
      have := mul_le_mul_of_nonneg_right hr1 (mul_nonneg hr0.le (sq_nonneg n))
      linarith
    have hrn2 : 0 ≤ r * n ^ 2 := mul_nonneg hr0.le (sq_nonneg n)
    linarith

end NashWilliams18
