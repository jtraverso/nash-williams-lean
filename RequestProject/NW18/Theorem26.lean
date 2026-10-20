/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.SubgraphLift
import RequestProject.NW18.Lemma116
import RequestProject.FracStab.Main

/-!
# Theorem 2.6 (robust regular fractional decompositions), from Theorem 1.6

Following §11 of the paper, Theorem 2.6 is derived from
* `theorem_1_6` — Theorem 1.6, the stability version of the Fractional Nash-Williams
  Conjecture (main result of Part II of the paper), and
* `lemma_11_6` — Lemma 11.6 (random induced subgraphs of a non-extremal graph are, with high
  probability, non-extremal with high minimum degree), stated in counting form; the paper derives
  it from the estimability of max-cut (Theorem 11.4, a result from the property-testing
  literature) and Chernoff bounds; it is proved in `RequestProject.NW18.Lemma116`,

together with the deterministic averaging argument of Lemmas 11.8–11.10, which is fully proved
here (`prop_11_8`, `lemma_11_9`, `exists_edge_partition`, `good_set_achievable` and the proof of
`theorem_2_6`).

**Status:** fully proved. `lemma_11_6` is proved (`lemma_11_6_proof`); `theorem_1_6` is proved in
`RequestProject.FracStab.Main` (`theorem_1_6_proof`) from Theorem 10.9 of the paper
(`NashWilliams.Frac.rules_nonneg`, proved, together with Lemma 9.6 `local_structure`).
-/

namespace NashWilliams18

open Finset

/-- **Theorem 1.6** (Fractional stability). For each sufficiently small `σ > 0` there is
`ε > 0` such that for all large `n`: every graph `G` on `n` vertices with
`δ(G) ≥ (3/4 - ε) n` and no fractional triangle decomposition is `σ`-extremal.
(Main result of Part II of the paper; proved in `RequestProject.FracStab.Main` from
`NashWilliams.Frac.rules_nonneg`, the core of Theorem 10.9.) -/
theorem theorem_1_6 :
    ∃ σ₀ : ℝ, 0 < σ₀ ∧ ∀ σ : ℝ, 0 < σ → σ ≤ σ₀ → ∃ ε : ℝ, 0 < ε ∧ ∃ n₀ : ℕ,
      ∀ (W : Type) [Fintype W] [DecidableEq W] (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
        n₀ ≤ Fintype.card W → (3 / 4 - ε) * (Fintype.card W : ℝ) ≤ (Gr.minDegree : ℝ) →
        ¬ NashWilliams.HasFractionalTriangleDecomposition Gr → IsExtremal σ Gr :=
  NashWilliams.Frac.theorem_1_6_proof

open Classical in
/-- **Lemma 11.6** (counting form). For all `ε, ρ, σ > 0` and all large `k`, for all large `n`:
if `G` has `n` vertices, `δ(G) ≥ (3/4 - ε) n` and `G` is not `σ`-extremal, then for every edge
`uv` at least a `(1 - ρ)`-fraction of the `k`-sets containing `u, v` are good.
(Proved in `RequestProject.NW18.Lemma116`, following the paper: Chernoff-type bounds and the
estimability of max-cut, Theorem 11.4, for uniformly random samples.) -/
theorem lemma_11_6 :
    ∀ ε ρ σ : ℝ, 0 < ε → 0 < ρ → 0 < σ → ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → ∃ n₁ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₁ ≤ Fintype.card V → (3 / 4 - ε) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ¬ IsExtremal σ G → ∀ u v, G.Adj u v →
        (1 - ρ) * ((Fintype.card V - 2).choose (k - 2) : ℝ) ≤
          ((((univ : Finset V).powersetCard k).filter
            (fun S => u ∈ S ∧ v ∈ S ∧ IsGoodSet G ε σ S)).card : ℝ) :=
  lemma_11_6_proof

lemma card_filter_mem_edgeFinset {W : Type*} [Fintype W] [DecidableEq W] (Gr : SimpleGraph W)
    [DecidableRel Gr.Adj] (v : W) :
    (Gr.edgeFinset.filter (fun e => v ∈ e)).card = Gr.degree v := by
  rw [← Gr.card_incidenceFinset_eq_degree, Gr.incidenceFinset_eq_filter]

/-- Lemma 11.10, the part concerning one good set: on a good set `S`, every target `φ` with
values in `[1 - 1/C', 1]` is the load of a fractional triangle packing of `G[S]` (lifted to
`G`), provided Theorem 1.6 holds for `σ/4`. -/
theorem good_set_achievable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {σ ε ε₁ : ℝ} (hσ : 0 ≤ σ) {n₁ : ℕ}
    (h16 : ∀ (W : Type) [Fintype W] [DecidableEq W] (Gr : SimpleGraph W) [DecidableRel Gr.Adj],
      n₁ ≤ Fintype.card W → (3 / 4 - ε₁) * (Fintype.card W : ℝ) ≤ (Gr.minDegree : ℝ) →
      ¬ NashWilliams.HasFractionalTriangleDecomposition Gr → IsExtremal (σ / 4) Gr)
    (S : Finset V) (hS : IsGoodSet G ε σ S) (hk : n₁ ≤ S.card)
    (d C' : ℕ) (hd : 2 * ε * S.card + d ≤ ε₁ * S.card) (hdσ : (d : ℝ) ≤ σ * S.card / 4)
    (hC' : 1 ≤ C') (hC'd : 2 * S.card ≤ C' * d)
    (φ : Sym2 V → ℝ) (hφ : ∀ u v, u ∈ S → v ∈ S → G.Adj u v →
      1 - 1 / (C' : ℝ) ≤ φ s(u, v) ∧ φ s(u, v) ≤ 1) :
    ∃ ψ : Finset V → ℝ, (∀ T, 0 ≤ ψ T) ∧ (∀ T, ¬ T ⊆ S → ψ T = 0) ∧
      (∀ T ∈ G.cliqueFinset 3, ψ T ≤ 1) ∧
      ∀ u v, G.Adj u v → load G ψ u v = if u ∈ S ∧ v ∈ S then φ s(u, v) else 0 := by
  set Gs := G.induce (S : Set V)
  have hcard : Fintype.card (S : Set V) = S.card := by simp
  -- robustness of `G[S]` under deletions, by Theorem 1.6
  have hfrac : ∀ H : Finset (Sym2 (S : Set V)), (∀ v, (H.filter (fun f => v ∈ f)).card ≤ d) →
      NashWilliams.HasFractionalTriangleDecomposition (del Gs H) := by
    intro H hH
    by_contra hno
    have hmin := minDegree_deleteEdges_ge Gs H d hH
    have hmin' : ((Gs.minDegree : ℕ) : ℝ) ≤ (del Gs H).minDegree + d := by exact_mod_cast hmin
    have hδ : (3 / 4 - ε₁) * (Fintype.card (S : Set V) : ℝ) ≤ ((del Gs H).minDegree : ℝ) := by
      rw [hcard]; have := hS.1; linarith
    refine not_extremal_deleteEdges Gs hσ H d hH (by rw [hcard]; exact hdσ) hS.2
      (h16 _ (del Gs H) (by rw [hcard]; exact hk) hδ hno)
  -- an edge partition of `G[S]`
  obtain ⟨c, hc⟩ := exists_edge_partition S.card d C' hC' hC'd Gs.edgeFinset
    (fun e he => Gs.not_isDiag_of_mem_edgeSet (by simpa using he)) (fun v => by
      rw [card_filter_mem_edgeFinset, ← hcard]
      exact (Gs.degree_lt_card_verts v).le)
  -- Lemma 11.9 on `G[S]`
  obtain ⟨ψ', hψ'0, hψ'⟩ := lemma_11_9 Gs d C' hC' c hc hfrac (fun e => φ (e.map Subtype.val))
    (fun e he => by
      induction e using Sym2.ind with
      | _ a b =>
        have hab : Gs.Adj a b := by simpa using he
        simpa using hφ a b (by simp) (by simp) hab)
  refine ⟨liftW S ψ', liftW_nonneg S hψ'0, fun T hT => liftW_of_not_subset S ψ' hT,
    fun T hT => ?_, fun u v huv => ?_⟩
  · by_cases hTS : T ⊆ S
    · simp only [liftW, if_pos hTS]
      set T' := T.subtype (· ∈ (S : Set V))
      have hT' : Gs.IsNClique 3 T' := by
        rw [isNClique_induce_iff, map_subtype_eq S T hTS]
        simpa using hT
      obtain ⟨x, y, z, hxy, hxz, hyz, hT'eq⟩ := card_eq_three.mp hT'.2
      have hxy' : Gs.Adj x y := hT'.1 (by simp [hT'eq]) (by simp [hT'eq]) hxy
      have hload := hψ' x y hxy'
      have hle : ψ' T' ≤ load Gs ψ' x y := by
        unfold load
        refine single_le_sum (f := ψ') (fun t _ => hψ'0 t) ?_
        simp only [mem_filter, SimpleGraph.mem_cliqueFinset_iff]
        exact ⟨hT', by simp [hT'eq], by simp [hT'eq]⟩
      have := (hφ x.1 y.1 (by simp) (by simp) hxy').2
      simp only [Sym2.map_mk] at hload
      linarith
    · simp [liftW, hTS]
  · by_cases h : u ∈ S ∧ v ∈ S
    · rw [if_pos h, load_liftW G S ψ' h.1 h.2, hψ' ⟨u, by simpa using h.1⟩ ⟨v, by simpa using h.2⟩ huv]
      simp
    · rw [if_neg h, load_liftW_of_not_mem G S ψ' h]

end NashWilliams18
