/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case125.Theorem146
import RequestProject.NW18.Case125.Lemma159
import RequestProject.NW18.Case125.Lemma156
import RequestProject.NW18.Case125.SideClose
import RequestProject.NW18.Case125.Reserve
import RequestProject.NW18.Case125.Residual

/-!
# Proof of Theorem 12.5 (case (2) of §12.2)

The proof of §15.3 of the paper:

1. take a max-cut bipartition `p` (`exists_maxcut_partition`); `G` is `β`-extremal as a
   2-partitioned graph and `IntDeg ≤ CrossDeg`, hence `β`-cross-balanced;
2. Lemma 15.6 (`lemma_15_6`) for `A = {v : IntDeg(v) ≥ (1/4 + 2√β) n}`;
3. one side `G[V_i]` is not `α/24`-close to `T₂` or `T̄₂` (`exists_side_not_close`);
4. a reserve `T₀` of `≥ 2√β n²` interior triangles in `G − A` (`claim_12_5_1`);
5. Lemma 15.9 (`lemma_15_9`) gives a packing `T` saturating `A` with a cross-divisible
   residual `G' = (G − E(T)) \ A` of large minimum degree;
6. Theorem 14.6 (hypothesis `h146 : Theorem146Statement`; `theorem_14_6` derives it from `h1316`) applied to `G'` (whose hypotheses are
   `isIntDiv_residual`, `isF0Idealized_residual`, `not_isSideClose_residual`) gives an
   `F₀`-decomposition of `G'`, and `T` together with it is a triangle decomposition of `G`
   (`hasTriangleDecomposition_of_residual`).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F0)

set_option maxHeartbeats 1000000 in
/-- **Theorem 12.5**, proof (same statement as `theorem_12_5` in `Cases.lean`). -/
theorem theorem_12_5_of_146 (h146 : Theorem146Statement) :
    ∀ α : ℝ, 0 < α → ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsExtremal β G → ¬ IsCloseToExtremal α G →
        NashWilliams.HasTriangleDecomposition G := by
  intro α hα
  set θ := α / 24 with hθdef
  have hθ : 0 < θ := by positivity
  obtain ⟨β₁, hβ₁, n₁, hside⟩ := exists_side_not_close α hα
  obtain ⟨κ, hκ, β₂, hβ₂, n₂, hres⟩ := claim_12_5_1 θ hθ
  obtain ⟨ε₀, hε₀, n₃, h146⟩ := h146 (θ / 2) (by positivity)
  obtain ⟨γ₀, hγ₀, h159⟩ := lemma_15_9
  -- the parameter `s = √β`
  set s : ℝ := min (min (min (Real.sqrt β₁) (Real.sqrt β₂)) (min (Real.sqrt γ₀) (1 / 320)))
    (min (κ / 2) (min (ε₀ / 40) (θ / 160))) with hsdef
  have hs : 0 < s := by
    simp only [hsdef, lt_min_iff]
    refine ⟨⟨⟨Real.sqrt_pos.mpr hβ₁, Real.sqrt_pos.mpr hβ₂⟩, Real.sqrt_pos.mpr hγ₀,
      by norm_num⟩, by positivity, by positivity, by positivity⟩
  have hs1 : s ≤ Real.sqrt β₁ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
    (min_le_left _ _))
  have hs2 : s ≤ Real.sqrt β₂ := le_trans (min_le_left _ _) (le_trans (min_le_left _ _)
    (min_le_right _ _))
  have hs3 : s ≤ Real.sqrt γ₀ := le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
    (min_le_left _ _))
  have hs4 : s ≤ 1 / 320 := le_trans (min_le_left _ _) (le_trans (min_le_right _ _)
    (min_le_right _ _))
  have hs5 : s ≤ κ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hs6 : s ≤ ε₀ / 40 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (min_le_left _ _))
  have hs7 : s ≤ θ / 160 := le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (min_le_right _ _))
  set β : ℝ := s ^ 2 with hβdef
  have hβ : 0 < β := by positivity
  have hsqβ : Real.sqrt β = s := by rw [hβdef, Real.sqrt_sq hs.le]
  have sq_le : ∀ {x : ℝ}, 0 < x → s ≤ Real.sqrt x → β ≤ x := by
    intro x hx h
    have := pow_le_pow_left₀ hs.le h 2
    rwa [Real.sq_sqrt hx.le] at this
  have hββ₁ : β ≤ β₁ := sq_le hβ₁ hs1
  have hββ₂ : β ≤ β₂ := sq_le hβ₂ hs2
  have hβγ₀ : β ≤ γ₀ := sq_le hγ₀ hs3
  have hβ100 : β ≤ 1 / 100 := by
    have : s ^ 2 ≤ (1 / 320) ^ 2 := pow_le_pow_left₀ hs.le hs4 2
    rw [hβdef]; linarith
  obtain ⟨n₄, h159'⟩ := h159 β hβ hβγ₀
  refine ⟨β, hβ, max (max (max n₁ n₂) (max n₄ (2 * n₃ + 2))) (⌈12 / θ⌉₊ + 1),
    fun V _ _ G _ hn hdiv hδ hext hnc => ?_⟩
  have hn₁ : n₁ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₄ : n₄ ≤ Fintype.card V := le_trans (by omega) hn
  have hn₃ : 2 * n₃ + 2 ≤ Fintype.card V := le_trans (by omega) hn
  have hnθ : 12 / θ ≤ (Fintype.card V : ℝ) := by
    have h1 : ⌈12 / θ⌉₊ + 1 ≤ Fintype.card V := le_trans (le_max_right _ _) hn
    have h2 := Nat.le_ceil (12 / θ)
    have h3 : ((⌈12 / θ⌉₊ + 1 : ℕ) : ℝ) ≤ Fintype.card V := by exact_mod_cast h1
    push_cast at h3; linarith
  have hnpos : (0 : ℝ) < (Fintype.card V : ℝ) := by
    have : 0 < Fintype.card V := by omega
    exact_mod_cast this
  -- 1. max-cut bipartition
  obtain ⟨p, hp2, hmax⟩ := exists_maxcut_partition G hext
  -- 2. Lemma 15.6
  obtain ⟨hA, hcl, hgood⟩ := lemma_15_6 hβ hβ100 G p hδ hp2
  rw [hsqβ] at hA hcl hgood
  set A : Finset V := univ.filter (fun v => (1 / 4 + 2 * s) * Fintype.card V ≤
    (partDeg G p v (p v) : ℝ)) with hAdef
  have hnotA : ∀ v, v ∉ A → (partDeg G p v (p v) : ℝ) < (1 / 4 + 2 * s) * (Fintype.card V : ℝ) := by
    intro v hv
    simp only [hAdef, mem_filter, mem_univ, true_and, not_le] at hv
    exact hv
  -- 3. one side is not close
  obtain ⟨i, hi⟩ := hside V G p β hβ.le hββ₁ hn₁ hp2.2 hnc
  -- 4. the reserve
  obtain ⟨T₀, hT₀, hT₀int, hT₀A, hT₀card⟩ := hres V G p A β hβ hββ₂ hn₂ hδ
    (by rw [hsqβ]; exact hA) (fun v hv => by rw [hsqβ]; exact (hnotA v hv).le)
    (fun j => by rw [hsqβ]; exact hcl j) ⟨i, hi⟩
  -- 5. Lemma 15.9
  have hbal : IsCrossBalanced β G p := by
    intro v j hj
    have := hmax v j hj
    have h' : (partDeg G p v (p v) : ℝ) ≤ partDeg G p v j := by exact_mod_cast this
    nlinarith
  obtain ⟨T, hT, hcov, hsur, hdeg, hTedges⟩ := h159' V G p T₀ A hn₄ hdiv hδ hp2 hbal hT₀
    hT₀int hT₀A (by rw [hsqβ]; nlinarith)
    (fun v hv => by
      simp only [hAdef, mem_filter, mem_univ, true_and]
      have : (1 / 4 + 2 * s) ≤ 0.371 := by norm_num at hs4 ⊢; linarith
      nlinarith)
    (by rw [hsqβ]; exact hA)
  rw [hsqβ] at hdeg hTedges
  set C := T.biUnion triEdges with hCdef
  have hCsub : C ⊆ G.edgeFinset :=
    biUnion_subset.mpr fun t ht => triEdges_subset_of_isNClique (hT.1 t ht)
  -- 6. Theorem 14.6 for the cleaned graph
  have hcardA : (Fintype.card {x // x ∈ Aᶜ} : ℝ) = (Fintype.card V : ℝ) - A.card := by
    rw [Fintype.card_coe, card_compl]
    have : A.card ≤ Fintype.card V := card_le_univ A
    push_cast [this]; ring
  have hdeg' : ∀ a : {x // x ∈ Aᶜ}, (3 / 4 - 7 * Real.sqrt β) * ((Fintype.card V : ℝ) - A.card) ≤
      ((residualGraph G A C).degree a : ℝ) := by
    intro a
    rw [residual_degree_eq G A C hCsub hcov a, hsqβ]
    exact hdeg a.1 (mem_compl.mp a.2)
  have hid := isF0Idealized_residual G p A C
    (le_min (by rw [hsqβ]; linarith) (by rw [hsqβ]; linarith)) (min_le_right ε₀ (1 / 8))
    (by rw [hsqβ]; exact hA) (fun j => by rw [hsqβ]; exact hcl j)
    (fun v hv => by rw [hsqβ]; exact (hnotA v hv).le) hdeg'
  have hint := isIntDiv_residual G p A T hdiv hT hcov hsur
  have hDi : (Fintype.card V : ℝ) / 3 ≤ ((partClass p i).card : ℝ) := by
    have := hcl i; nlinarith
  have hside' := not_isSideClose_residual G p A C hθ (by rw [hsqβ]; linarith) hnθ
    (by rw [hsqβ]; exact hA) (by rw [hsqβ]; exact hTedges) i hDi hi
  have hn' : n₃ ≤ Fintype.card {x // x ∈ Aᶜ} := by
    have h1 : (n₃ : ℝ) ≤ (Fintype.card V : ℝ) / 2 - 1 := by
      have : ((2 * n₃ + 2 : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn₃
      push_cast at this; linarith
    have h2 : (A.card : ℝ) ≤ (Fintype.card V : ℝ) / 2 := by nlinarith
    have : (n₃ : ℝ) ≤ Fintype.card {x // x ∈ Aᶜ} := by rw [hcardA]; linarith
    exact_mod_cast this
  obtain ⟨D, hD⟩ := h146 {x // x ∈ Aᶜ} (fun a => p a.1) (residualGraph G A C) hn' hint
    (hid.mono (min_le_left _ _)) ⟨i, hside'⟩
  exact hasTriangleDecomposition_of_residual G A T hT.1 hT.2 hcov (fun a => p a.1) F0 D hD

/-- **Theorem 12.5** from the global interface `Theorem1316Statement` (kept for compatibility;
see `theorem_12_5_of_146` for the version with the specialised premise). -/
theorem theorem_12_5_proof (h1316 : Theorem1316Statement) :
    ∀ α : ℝ, 0 < α → ∃ β : ℝ, 0 < β ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → IsExtremal β G → ¬ IsCloseToExtremal α G →
        NashWilliams.HasTriangleDecomposition G :=
  theorem_12_5_of_146 (theorem_14_6 h1316)

end NashWilliams18
