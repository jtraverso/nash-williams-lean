/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.Claim1594W

/-!
# Lemma 15.9 with a protected edge set

`lemma_15_9_W` is Lemma 15.9 (case `E = ∅` replaced by an arbitrary protected set `W` of
edges, at most `4` at every vertex and an even number at every vertex of `A`, avoided by the
reserve).  The packing avoids `W` and covers every edge at `A` except those of `W`.  The proof
is the proof of `lemma_15_9`, with `oddball_induction_W` in place of Claim 15.9.4; it requires
`|A| ≤ √γ n` (instead of `2 √γ n`), which leaves room for the protected edges.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

theorem lemma_15_9_W :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
        (p : V → Fin 2) (T₀ : Finset (Finset V)) (A : Finset V) (W : Finset (Sym2 V)),
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree →
        IsTwoExtremal γ G p → IsCrossBalanced γ G p →
        IsTrianglePacking G T₀ → (∀ s ∈ T₀, ∃ i, ∀ x ∈ s, p x = i) →
        (∀ s ∈ T₀, ∀ x ∈ s, x ∉ A) → Disjoint (T₀.biUnion triEdges) W →
        2 * Real.sqrt γ * (Fintype.card V : ℝ) ^ 2 ≤ (T₀.card : ℝ) →
        (∀ v, 0.371 * (Fintype.card V : ℝ) ≤ (partDeg G p v (p v) : ℝ) → v ∈ A) →
        (A.card : ℝ) ≤ Real.sqrt γ * Fintype.card V →
        W ⊆ G.edgeFinset → (∀ x, (W.filter (fun e => x ∈ e)).card ≤ 4) →
        (∀ a ∈ A, Even (W.filter (fun e => a ∈ e)).card) →
        ∃ T : Finset (Finset V), IsTrianglePacking G T ∧
          Disjoint (T.biUnion triEdges) W ∧
          (∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → s(u, v) ∉ W → s(u, v) ∈ T.biUnion triEdges) ∧
          intSurplus p (G.edgeFinset \ T.biUnion triEdges) = 0 ∧
          (∀ v, v ∉ A → (3 / 4 - 7 * Real.sqrt γ) * ((Fintype.card V : ℝ) - A.card) ≤
            (((G.edgeFinset \ T.biUnion triEdges).filter (fun e => v ∈ e)).card : ℝ)) := by
  refine ⟨1 / 1000000, by norm_num, fun γ hγ hγ₀ => ?_⟩
  have hγ2 : γ ≤ 1 / 10000 := hγ₀.trans (by norm_num)
  set r := Real.sqrt γ with hrdef
  have hr0 : 0 < r := Real.sqrt_pos.mpr hγ
  have hr1 : r ≤ 1 / 1000 := by
    have : r ≤ Real.sqrt ((1 / 1000) ^ 2) := Real.sqrt_le_sqrt (by linarith)
    rwa [Real.sqrt_sq (by norm_num)] at this
  have hrr : r * r = γ := Real.mul_self_sqrt hγ.le
  refine ⟨⌈100 / r⌉₊ + 1, fun V _ _ G _ p T₀ A W hn hdiv hδ hext hbal hT₀ hT₀int hT₀A hT₀W
    hT₀card hB hA hWG hWx hWev => ?_⟩
  classical
  set n : ℝ := (Fintype.card V : ℝ) with hndef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hrn : 100 ≤ r * n := by
    have h1 : ((⌈100 / r⌉₊ + 1 : ℕ) : ℝ) ≤ n := by rw [hndef]; exact_mod_cast hn
    have h2 := Nat.le_ceil (100 / r)
    push_cast at h1
    have : 100 / r ≤ n := by linarith
    rw [div_le_iff₀ hr0] at this; linarith
  have hn20 : 20 ≤ r * n := by linarith
  obtain ⟨hAs, hcl, hnormal⟩ := lemma_15_6 hγ (by linarith) G p hδ hext
  set Astar := univ.filter (fun v => (1 / 4 + 2 * r) * n ≤ (partDeg G p v (p v) : ℝ)) with hAstar
  have hV : ∀ i, ((partClass p i).card : ℝ) ≤ (1 + r) * n / 2 := by
    intro i
    obtain ⟨j, hj, -⟩ := fin2_exists_ne i
    have h1 := hcl j
    have h2 : ((partClass p i).card : ℝ) + (partClass p j).card = n := by
      rw [hndef]; exact_mod_cast card_partClass_add' p (Ne.symm hj)
    linarith
  have hnorm : ∀ v, v ∉ Astar → (1 / 4 - r) * n ≤ (partDeg G p v (p v) : ℝ) ∧
      ∀ i, i ≠ p v → (1 / 2 - 2 * r) * n ≤ (partDeg G p v i : ℝ) := by
    intro v hv
    have : (partDeg G p v (p v) : ℝ) < (1 / 4 + 2 * r) * n := by
      by_contra h
      exact hv (mem_filter.mpr ⟨mem_univ _, le_of_not_gt h⟩)
    exact hnormal v this
  -- Claim 15.9.3: a low-degree subpacking `T'` of the reserve
  obtain ⟨T', hT'T₀, hT'card, hT'deg⟩ := claim_15_9_3 G hT₀ hγ (by linarith) hn20 hT₀card
  have hT'pack : IsTrianglePacking G T' :=
    ⟨fun t ht => hT₀.1 t (hT'T₀ ht), hT₀.2.subset (by exact_mod_cast hT'T₀)⟩
  have hT'int : ∀ s ∈ T', IsInteriorTri p s := fun s hs => hT₀int s (hT'T₀ hs)
  have hT'A : ∀ s ∈ T', ∀ x ∈ s, x ∉ A := fun s hs => hT₀A s (hT'T₀ hs)
  -- Claim 15.9.4 with protected edges
  obtain ⟨T₁, hT₁, hdisj, hdisjW, hmeet, hcov, hint1, -⟩ := oddball_induction_W G p T' W A Astar
    hr0 hr1 hrr.symm hrn hδ hbal hV hnorm hAs hdiv.2 hT'pack hT'A
    hT'deg hWG hWx hWev hA A subset_rfl
  have hint1 : ((T₁.filter (fun t => IsInteriorTri p t)).card : ℝ) ≤
      0.01 * (Fintype.card V : ℝ) *
        ((univ.filter (fun v => 0.371 * (Fintype.card V : ℝ) ≤
          (partDeg G p v (p v) : ℝ))).card : ℝ) := by
    refine hint1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast card_le_card (filter_subset_filter _ (subset_univ A))
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
  refine ⟨T₁ ∪ T₂, ⟨fun s hs => ?_, ?_⟩, ?_, fun u v huv huA huW => ?_, ?_, fun v hv => ?_⟩
  · rcases mem_union.mp hs with h | h
    · exact hT₁.1 s h
    · exact hT₂pack.1 s h
  · rw [coe_union, Set.pairwiseDisjoint_union]
    refine ⟨hT₁.2, hT₂pack.2, fun i hi j hj _ => ?_⟩
    exact hdisj.mono (subset_biUnion_of_mem _ hi) (subset_biUnion_of_mem _ (hT₂T' hj))
  · rw [hunion]
    refine disjoint_union_left.mpr ⟨hdisjW, ?_⟩
    exact disjoint_of_subset_left (hC₂C'.trans (biUnion_subset_biUnion_of_subset_left _ hT'T₀))
      hT₀W
  · rw [hunion]; exact mem_union_left _ (hcov u v huv huA huW)
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
    have hrA : r * A.card ≤ r * (2 * r * n) := mul_le_mul_of_nonneg_left (hA.trans (by nlinarith)) hr0.le
    have hrn : r * r * n ≤ 1 / 100 * r * n := by
      have := mul_le_mul_of_nonneg_right hr1 (mul_nonneg hr0.le hn0)
      linarith
    have hrn0 : 0 ≤ r * n := mul_nonneg hr0.le hn0
    linarith

end NashWilliams18
