/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case127.TotPacking
public import RequestProject.NW18.Case127.Reserve
public import RequestProject.NW18.Case127.Residual

@[expose] public section

/-!
# Theorem 12.7, combinatorial core

`core_12_7`: there is `s > 0` such that every large triangle-divisible graph `G` with
`δ(G) ≥ 3n/4`, given with a four-partition `p` and a set `A` satisfying `Setup127 G p A s`
(classes of size `n/4 ± 1`, `|A| ≤ 2 s n`, at most `s n` `F₂`-abnormal pairs at every vertex
outside `A`), has a triangle decomposition.  This is the proof of Theorem 12.7 in §15.6 of the
paper:

1. a parity-fixer `v; w₀, …, w₃` (Claim 12.7.3, `exists_fixer`) with edge set `W`;
2. a reserve of interior triangles (Claim 12.7.6, `reserve_127`);
3. Lemma 15.9 with the protected set `W` (`lemma_15_9_W`) for the bipartition `P*`
   (hypotheses: Claims 12.7.4, 12.7.5), giving `T₁`;
4. Lemma 15.17 for the abnormal edges left (Claim 12.7.7, `step_15_17`), giving `T₂`;
5. one of the two fixer pairs `Q` makes `E₀₀ + E₀₂ − E₀₃` divisible by `4` (Claim 12.7.8,
   `even_parity_F2`, `parity_swap_F2`), which with cross-divisibility gives integral
   `F₂`-divisibility (Lemma 13.20);
6. Theorem 14.7 for `F₂` (from Theorem 13.16) decomposes the rest (`finish_127`).
-/

namespace NashWilliams18.C127

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F2)

set_option maxHeartbeats 1000000 in
/-- **Theorem 12.7**, combinatorial core. -/
theorem core_12_7_of_147 (h147 : Theorem147F2Statement) :
    ∃ s : ℝ, 0 < s ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (p : V → Fin 4) (A : Finset V), n₀ ≤ Fintype.card V →
      NashWilliams.IsTriangleDivisible G → Setup127 G p A s →
      NashWilliams.HasTriangleDecomposition G := by
  obtain ⟨ε, hε, n₁, h147⟩ := h147
  obtain ⟨γ₀, hγ₀, h159⟩ := lemma_15_9_W
  set r : ℝ := min (min (1 / 2000) (ε / 100)) (Real.sqrt γ₀) with hrdef
  have hr0 : 0 < r := lt_min (lt_min (by norm_num) (by positivity)) (Real.sqrt_pos.mpr hγ₀)
  have hr1 : r ≤ 1 / 2000 := (min_le_left _ _).trans (min_le_left _ _)
  have hr2 : r ≤ ε / 100 := (min_le_left _ _).trans (min_le_right _ _)
  have hr3 : r ≤ Real.sqrt γ₀ := min_le_right _ _
  set γ : ℝ := r ^ 2 with hγdef
  have hγ : 0 < γ := by positivity
  have hγγ₀ : γ ≤ γ₀ := by
    have := pow_le_pow_left₀ hr0.le hr3 2
    rwa [Real.sq_sqrt hγ₀.le] at this
  obtain ⟨n₂, h159'⟩ := h159 γ hγ hγγ₀
  set s : ℝ := γ / 100 with hsdef
  have hs0 : 0 < s := by positivity
  have hs1 : s ≤ 1 / 1000 := by
    have : r ^ 2 ≤ (1 / 2000) ^ 2 := pow_le_pow_left₀ hr0.le hr1 2
    rw [hsdef, hγdef]; nlinarith
  have hsr : s ≤ r / 200000 := by
    rw [hsdef, hγdef]
    have : r * r ≤ r * (1 / 2000) := mul_le_mul_of_nonneg_left hr1 hr0.le
    nlinarith
  have hsqγ : Real.sqrt γ = r := by rw [hγdef, Real.sqrt_sq hr0.le]
  have h100s : 100 * s = γ := by rw [hsdef]; ring
  refine ⟨s, hs0, max (max (2 * n₁) n₂) (⌈1000 / s⌉₊ + 1),
    fun V _ _ G _ p A hn hdiv hS => ?_⟩
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₁ : 2 * n₁ ≤ Fintype.card V := le_trans (by omega) hn
  have hsn : 1000 ≤ s * n := by
    have h1 : ((⌈1000 / s⌉₊ + 1 : ℕ) : ℝ) ≤ n := by
      rw [hndef]; exact_mod_cast le_trans (le_max_right _ _) hn
    have h2 := Nat.le_ceil (1000 / s)
    push_cast at h1
    have : 1000 / s ≤ n := by linarith
    rw [div_le_iff₀ hs0] at this; linarith
  have hrn : 1000 ≤ r * n := by
    have : s * n ≤ r * n := mul_le_mul_of_nonneg_right (by linarith) hn0
    linarith
  have hA := hS.A_card
  have hAr : (A.card : ℝ) ≤ r * n / 100 := by nlinarith
  -- 1. the parity-fixer
  obtain ⟨v, w0, w1, w2, w3, hF⟩ := exists_fixer hS (by linarith) (by nlinarith)
  set W := fixW v w0 w1 w2 w3 with hWdef
  have hq0 : sideP G p A w0 = 0 := by rw [sideP_of_not_mem hF.n0, hF.c0]; decide
  have hq1 : sideP G p A w1 = 0 := by rw [sideP_of_not_mem hF.n1, hF.c1]; decide
  have hq2 : sideP G p A w2 = 1 := by rw [sideP_of_not_mem hF.n2, hF.c2]; decide
  have hq3 : sideP G p A w3 = 1 := by rw [sideP_of_not_mem hF.n3, hF.c3]; decide
  -- 2. the reserve
  obtain ⟨T₀, hT₀, hT₀int, hT₀A, hT₀W, hT₀c⟩ := reserve_127 hS hs1 (by linarith) hF
  -- 3. Lemma 15.9 with protected edges `W`
  have hext := twoExtremal_127 hS hs1 (by linarith)
  have hbal := crossBalanced_127 hS (by linarith)
  rw [h100s] at hext hbal
  obtain ⟨T1, hT1, hT1W, hcov1, hsur1, hdeg1⟩ := h159' V G (sideP G p A) T₀ A W hn₂ hdiv hS.deg
    hext hbal hT₀ hT₀int hT₀A hT₀W
    (by rw [hsqγ]; nlinarith)
    (fun x hx => highInt_mem_127 hS hs1 (by linarith) x hx)
    (by rw [hsqγ]; linarith)
    (fixW_subset hF) (fixW_filter_card_le hF) (fixW_filter_even hF)
  rw [hsqγ] at hdeg1
  set C1 := T1.biUnion triEdges with hC1
  have hC1G : C1 ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT1.1 t ht)
  have hC1deg : ∀ a, a ∉ A → ((C1.filter (fun e => a ∈ e)).card : ℝ) ≤ 8 * r * n := by
    intro a ha
    have h1 := hdeg1 a ha
    have h2 : ((G.edgeFinset \ C1).filter (fun e => a ∈ e)).card +
        (C1.filter (fun e => a ∈ e)).card = G.degree a := by
      rw [← card_edgeFinset_filter_mem, ← card_union_of_disjoint
        (disjoint_filter_filter sdiff_disjoint), ← filter_union, sdiff_union_of_subset hC1G]
    have h2R : (((G.edgeFinset \ C1).filter (fun e => a ∈ e)).card : ℝ) +
        (C1.filter (fun e => a ∈ e)).card = G.degree a := by exact_mod_cast h2
    have h3 := degree_le_normal hS a ha
    have h4 : (3 / 4 - 7 * r) * n - A.card ≤ (3 / 4 - 7 * r) * (n - A.card) := by
      have : 0 ≤ 3 / 4 - 7 * r := by linarith
      nlinarith
    nlinarith
  -- 4. Lemma 15.17 for the remaining abnormal edges
  obtain ⟨T2, hT2, hT2cov, hT2cross, hT2deg⟩ := step_15_17 hS hs1 hsn C1 W (8 * r * n)
    (by nlinarith) hC1deg (fixW_filter_card_le hF)
  set C2 := T2.biUnion triEdges with hC2
  -- 5./6. the total packing for a fixer pair `Q`
  have hcov1' : ∀ u v', G.Adj u v' → (u ∈ A ∨ v' ∈ A) → s(u, v') ∉ W → s(u, v') ∈ C1 :=
    fun u v' huv hA' _ => hcov1 u v' huv hA' (by assumption)
  have finishQ : ∀ Q, FixQ G p A (sideP G p A) W Q →
      (4 : ℤ) ∣ edgeVec p (G.edgeFinset \ (T1 ∪ T2 ∪ Q).biUnion triEdges) 0 0 +
        edgeVec p (G.edgeFinset \ (T1 ∪ T2 ∪ Q).biUnion triEdges) 0 2 -
        edgeVec p (G.edgeFinset \ (T1 ∪ T2 ∪ Q).biUnion triEdges) 0 3 →
      NashWilliams.HasTriangleDecomposition G := by
    intro Q hQ hmod
    obtain ⟨hTot, hcov, hbl, hsur, hdeg⟩ := tot_props W T1 T2 Q hT1 hT1W
      (fun u v' huv hA' hW => hcov1 u v' huv hA' hW) hsur1 hT2 hT2cov hT2cross hQ
    have hsum := intSurplus_side_F2 p (sideP G p A) (G.edgeFinset \ (T1 ∪ T2 ∪ Q).biUnion triEdges)
      (fun x y hxy => by
        obtain ⟨hxyG, hxyC⟩ := mem_sdiff.mp hxy
        have hadj := G.mem_edgeFinset.mp hxyG
        have hx : x ∉ A := fun hx => hxyC (hcov x y hadj (Or.inl hx))
        have hy : y ∉ A := fun hy => hxyC (hcov x y hadj (Or.inr hy))
        exact ⟨sideP_of_not_mem hx, sideP_of_not_mem hy, hbl x y hadj hxyC hx hy⟩)
    rw [hsur] at hsum
    have hdegR : ∀ a, a ∉ A → ((((T1 ∪ T2 ∪ Q).biUnion triEdges).filter
        (fun e => a ∈ e)).card : ℝ) ≤ 8 * r * n + 12 * s * n + 4 := by
      intro a ha
      have h1 := hdeg a
      have h2 := hC1deg a ha
      have h3 := hT2deg a
      have h4 := fixW_filter_card_le hF a
      have h1R : ((((T1 ∪ T2 ∪ Q).biUnion triEdges).filter (fun e => a ∈ e)).card : ℝ) ≤
          ((C1.filter (fun e => a ∈ e)).card : ℝ) + (C2.filter (fun e => a ∈ e)).card +
          (W.filter (fun e => a ∈ e)).card := by exact_mod_cast h1
      have h4R : ((W.filter (fun e => a ∈ e)).card : ℝ) ≤ 4 := by exact_mod_cast h4
      linarith
    have hεr : 100 * r ≤ ε := by linarith
    have hid := idealized_127 hS ((T1 ∪ T2 ∪ Q).biUnion triEdges) hbl
      (8 * r * n + 12 * s * n + 4) ε hdegR (by
        have : 100 * r * (n - A.card) ≤ ε * (n - A.card) :=
          mul_le_mul_of_nonneg_right hεr (by nlinarith)
        nlinarith)
      (by
        have : 100 * r * n ≤ ε * n := mul_le_mul_of_nonneg_right hεr hn0
        nlinarith)
    have hnA : n₁ ≤ Fintype.card {x // x ∈ Aᶜ} := by
      rw [Fintype.card_coe, card_compl]
      have hAn : (A.card : ℝ) ≤ n / 2 := by nlinarith
      have : A.card * 2 ≤ Fintype.card V := by
        have : (A.card : ℝ) * 2 ≤ n := by linarith
        rw [hndef] at this; exact_mod_cast this
      omega
    exact finish_127 h147 G hdiv p A (T1 ∪ T2 ∪ Q) hTot hcov hbl hmod
      (by linarith) hid hnA
  -- the parity choice (Claim 12.7.8)
  have hQA := fixQA_good hF (sideP G p A) hq0 hq1 hq2 hq3
  have hQB := fixQB_good hF (sideP G p A) hq0 hq1 hq2 hq3
  obtain ⟨hTotA, hcovA, hblA, -, -⟩ := tot_props W T1 T2 (fixQA v w0 w1 w2 w3) hT1 hT1W
    (fun u v' huv hA' hW => hcov1 u v' huv hA' hW) hsur1 hT2 hT2cov hT2cross hQA
  set EA := G.edgeFinset \ (T1 ∪ T2 ∪ fixQA v w0 w1 w2 w3).biUnion triEdges with hEA
  have hpar := even_parity_F2 (G := residualGraph G A ((T1 ∪ T2 ∪ fixQA v w0 w1 w2 w3).biUnion
    triEdges)) (p := fun a => p a.1)
    (fun a b hab => hblA a.1 b.1 hab.1 hab.2 (mem_compl.mp a.2) (mem_compl.mp b.2))
    (residual_even_degree G A _ hdiv hTotA hcovA)
  rw [residual_edgeVec G A _ hcovA p] at hpar
  by_cases h4 : (4 : ℤ) ∣ edgeVec p EA 0 0 + edgeVec p EA 0 2 - edgeVec p EA 0 3
  · exact finishQ _ hQA h4
  · -- the swapped pair
    have hWsub : W ⊆ G.edgeFinset \ (C1 ∪ C2) := by
      intro e he
      refine mem_sdiff.mpr ⟨fixW_subset hF he, fun h => ?_⟩
      rcases mem_union.mp h with h | h
      · exact disjoint_left.mp hT1W h he
      · obtain ⟨t, ht, het⟩ := mem_biUnion.mp h
        exact (clean_tri_edges (hT2.1 t ht) het).2.2 he
    obtain ⟨s00, s02, s03⟩ := parity_swap_F2 (p := p) hF _ hWsub
    have hsplit : ∀ Q : Finset (Finset V), G.edgeFinset \ (T1 ∪ T2 ∪ Q).biUnion triEdges =
        (G.edgeFinset \ (C1 ∪ C2)) \ Q.biUnion triEdges := by
      intro Q
      rw [union_biUnion, union_biUnion]
      ext e; simp only [mem_sdiff, mem_union]; tauto
    rw [← hsplit, ← hsplit] at s00 s02 s03
    rw [← hEA] at s00 s02 s03
    refine finishQ _ hQB ?_
    rw [s00, s02]
    obtain ⟨k, hk⟩ := hpar
    have hk' : edgeVec p EA 0 0 + edgeVec p EA 0 2 - edgeVec p EA 0 3 = k + k := hk
    have h03 : edgeVec p (G.edgeFinset \ (T1 ∪ T2 ∪ fixQB v w0 w1 w2 w3).biUnion triEdges) 0 3 =
        edgeVec p EA 0 3 - 1 := by linarith
    rw [h03]
    omega

/-- Combinatorial core of Theorem 12.7 from the global interface `Theorem1316Statement`
(kept for compatibility). -/
theorem core_12_7 (h1316 : Theorem1316Statement) :
    ∃ s : ℝ, 0 < s ∧ ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
      [DecidableRel G.Adj] (p : V → Fin 4) (A : Finset V), n₀ ≤ Fintype.card V →
      NashWilliams.IsTriangleDivisible G → Setup127 G p A s →
      NashWilliams.HasTriangleDecomposition G :=
  core_12_7_of_147 (theorem_14_7_F2 h1316)

end NashWilliams18.C127
