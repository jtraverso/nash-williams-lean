/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case124.Residual124
import RequestProject.NW18.Case124.Vortex.Main
import RequestProject.NW18.Case125.F0Producer

/-!
# Branch 12.4 by the bounded-core route: vortex, finite-core absorber, protected cover-down

This file fixes the exact interfaces of the bounded-core route for branch 12.4 and proves the
deterministic assembly.

* `CleanVortex124 G θ σ q M L U`: a vortex `U 0 = V ⊇ U 1 ⊇ ⋯ ⊇ U L` with sizes shrinking by
  a factor in `[7q/8, 9q/8]`, every non-final level of size `≥ M`, a final core of size `< M`,
  **parent-wide** degree control `d(v, U (i+1)) ≥ (3/4 - θ)|U (i+1)|` for all `v ∈ U i`,
  `δ(G[U i]) ≥ (3/4 - θ)|U i|`, and `G[U i]` not `σ/4`-extremal.
* `vortexSpec124` (**proved**): such vortices exist, with `M` as large as required.  This is
  `uniform_vortex124_parent`.
* `CoreAbsorberSpec124` (residual): one absorber `A` that avoids every edge inside a small set
  `U₁` and absorbs every divisible `L` inside a bounded core `U ⊆ U₁`.
* `VortexCoverSpec124` (residual): for a clean vortex and any sparse `A` avoiding `E(G[U 1])`,
  a decomposable `EQ ⊆ E(G) \ A` covers every edge outside `A ∪ E(G[U L])`.
* `branch124_of_bounded_core` (**proved**): the two residual propositions give the exact
  `Branch124Statement`; `nash_williams_of_bounded_core` then gives Theorem 1.8 (with the proved
  `theorem146Statement_holds`).
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges of `G` with both ends in `U`. -/
def insideEdges (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset ∩ triEdges U

lemma insideEdges_subset (G : SimpleGraph V) [DecidableRel G.Adj] (U : Finset V) :
    insideEdges G U ⊆ G.edgeFinset := inter_subset_left

lemma insideEdges_mono (G : SimpleGraph V) [DecidableRel G.Adj] {U W : Finset V} (h : U ⊆ W) :
    insideEdges G U ⊆ insideEdges G W := by
  intro e he
  rw [insideEdges, mem_inter] at he ⊢
  refine ⟨he.1, ?_⟩
  unfold triEdges at he ⊢
  rw [mem_filter] at he ⊢
  exact ⟨Finset.sym2_mono h he.2.1, he.2.2⟩

lemma mem_of_mem_insideEdges {G : SimpleGraph V} [DecidableRel G.Adj] {U : Finset V}
    {e : Sym2 V} (he : e ∈ insideEdges G U) {v : V} (hv : v ∈ e) : v ∈ U := by
  rw [insideEdges, mem_inter, triEdges, mem_filter] at he
  induction e using Sym2.ind with
  | _ x y =>
    rw [Finset.mk_mem_sym2_iff] at he
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact he.2.1.1
    · exact he.2.1.2

/-- A **clean vortex** for branch 12.4. -/
def CleanVortex124 (G : SimpleGraph V) [DecidableRel G.Adj] (θ σ q : ℝ) (M L : ℕ)
    (U : ℕ → Finset V) : Prop :=
  U 0 = univ ∧
  (∀ i < L, U (i + 1) ⊆ U i ∧ M ≤ (U i).card ∧
    7 * q / 8 * ((U i).card : ℝ) ≤ (U (i + 1)).card ∧
    ((U (i + 1)).card : ℝ) ≤ 9 * q / 8 * (U i).card) ∧
  (U L).card < M ∧ 0 < (U L).card ∧
  (∀ i < L, ∀ v ∈ U i,
    (3 / 4 - θ) * ((U (i + 1)).card : ℝ) ≤ (((U (i + 1)).filter (G.Adj v)).card : ℝ)) ∧
  ∀ i ≤ L, (3 / 4 - θ) * ((U i).card : ℝ) ≤ ((G.induce (U i : Set V)).minDegree : ℝ) ∧
    ¬ IsExtremal (σ / 4) (G.induce (U i : Set V))

lemma CleanVortex124.antitone {G : SimpleGraph V} [DecidableRel G.Adj] {θ σ q : ℝ} {M L : ℕ}
    {U : ℕ → Finset V} (h : CleanVortex124 G θ σ q M L U) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ L) :
    U j ⊆ U i := by
  induction j, hij using Nat.le_induction with
  | base => exact subset_rfl
  | succ j hij ih => exact ((h.2.1 j (by omega)).1).trans (ih (by omega))

/-- **Clean vortices exist** (proved, from `Vortex124.uniform_vortex124_parent`). -/
theorem vortexSpec124 (σ : ℝ) (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 8) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1) (q : ℝ) (hq0 : 0 < q) (hq1 : q ≤ 1 / 32) (Mlo : ℕ) :
    ∃ M N : ℕ, Mlo ≤ M ∧ 0 < M ∧ ∀ (V : Type) [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → (3 / 4 - θ / 2) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
      ¬ IsExtremal σ G → ∃ (L : ℕ) (U : ℕ → Finset V), CleanVortex124 G θ σ q M L U := by
  obtain ⟨M, N, hMlo, hM, h⟩ :=
    Vortex124.uniform_vortex124_parent σ hσ0 hσ1 θ hθ0 hθ1 ⟨q, hq0.le⟩ hq0 hq1 Mlo
  exact ⟨M, N, hMlo, hM, fun V _ _ G _ hN hδ hnx => h V G hN hδ hnx⟩

omit [Fintype V] in
/-- Every vertex has even degree in a triangle-decomposable loopless edge set. -/
lemma even_load_of_hasDecomp {E : Finset (Sym2 V)} (hE : ∀ e ∈ E, ¬ e.IsDiag)
    (h : HasDecomp onePart K3fam E) (v : V) : Even ((E.filter fun e => v ∈ e).card) :=
  ((OnePart.isIntDiv_part1_iff E hE).mp (isIntDiv_of_hasDecomp h)).2 v

/-- **Finite-core absorber** (residual proposition of the bounded-core route).  For a 12.4 host,
a small vertex set `U₁` (`|U₁| ≤ ζ n`) and a bounded core `U ⊆ U₁` (`|U| ≤ m`), there is a
sparse `A ⊆ E(G)` with no edge inside `U₁` such that `A ∪ L` is triangle-decomposable for
**every** divisible `L ⊆ E(G[U])`.  `ζ` depends only on `β`; `n₀` may depend on `m` and `ρ`. -/
def CoreAbsorberSpec124 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ ζ : ℝ, 0 < ζ ∧ ∀ (m : ℕ) (ρ : ℝ), 0 < ρ → ∃ n₀ : ℕ,
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 3 * Fintype.card V ≤ 4 * G.minDegree → ¬ IsExtremal β G →
      ∀ U U₁ : Finset V, U ⊆ U₁ → (U₁.card : ℝ) ≤ ζ * Fintype.card V → U.card ≤ m →
        ∃ A ⊆ G.edgeFinset, Disjoint A (insideEdges G U₁) ∧
          DegBounded A (ρ * Fintype.card V) ∧
          ∀ L ⊆ insideEdges G U, IsIntDiv onePart K3fam L → HasDecomp onePart K3fam (A ∪ L)

/-- **Protected cover-down along a clean vortex** (residual proposition of the bounded-core
route).  `θ` and `q₀` depend only on `β`; `ρ` and `M₀` on `β, q`.  For every clean vortex and
every sparse `A` with no edge inside `U 1`, some triangle-decomposable `EQ ⊆ E(G) \ A` covers
all edges of `G` outside `A` and outside the final core. -/
def VortexCoverSpec124 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧ ∃ q₀ : ℝ, 0 < q₀ ∧
    ∀ q : ℝ, 0 < q → q ≤ q₀ → ∃ ρ : ℝ, 0 < ρ ∧ ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M → ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
        n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → ¬ IsExtremal β G →
        ∀ (L : ℕ) (U : ℕ → Finset V), CleanVortex124 G θ β q M L U →
        ∀ A ⊆ G.edgeFinset, Disjoint A (insideEdges G (U 1)) →
          DegBounded A (ρ * Fintype.card V) → (∀ v, Even ((A.filter fun e => v ∈ e).card)) →
          ∃ EQ : Finset (Sym2 V), EQ ⊆ G.edgeFinset \ A ∧
            G.edgeFinset \ (A ∪ insideEdges G (U L)) ⊆ EQ ∧ HasDecomp onePart K3fam EQ

/-- **Branch 12.4 from the bounded-core propositions** (proved, deterministic assembly). -/
theorem branch124_of_bounded_core (hA : CoreAbsorberSpec124) (hC : VortexCoverSpec124) :
    Branch124Statement := by
  refine ⟨1 / 8, by norm_num, fun β hβ hβ8 => ?_⟩
  have hβ1 : β ≤ 1 := hβ8.trans (by norm_num)
  obtain ⟨θ, hθ0, hθ1, q₀, hq₀, hC'⟩ := hC β hβ hβ1
  obtain ⟨ζ, hζ, hA'⟩ := hA β hβ hβ1
  set q : ℝ := min (min q₀ (ζ / 2)) (1 / 32) with hq_def
  have hq0 : 0 < q := lt_min (lt_min hq₀ (by positivity)) (by norm_num)
  have hqq₀ : q ≤ q₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hqζ : q ≤ ζ / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hq32 : q ≤ 1 / 32 := min_le_right _ _
  obtain ⟨ρ, hρ, M₀, hC''⟩ := hC' q hq0 hqq₀
  obtain ⟨M, N, hMM₀, hM0, hvortex⟩ := vortexSpec124 β hβ hβ8 θ hθ0 hθ1 q hq0 hq32 M₀
  obtain ⟨n₁, hcover⟩ := hC'' M hMM₀
  obtain ⟨n₂, habsorb⟩ := hA' M ρ hρ
  refine ⟨max (max N n₁) (max n₂ M), fun V _ _ G _ hn hdiv hδ hnx => ?_⟩
  have hN : N ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn₁ : n₁ ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn₂ : n₂ ≤ Fintype.card V := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnM : M ≤ Fintype.card V := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hδ' : (3 / 4 - θ / 2) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) := by
    have : (3 * Fintype.card V : ℝ) ≤ 4 * G.minDegree := by exact_mod_cast hδ
    have : (0 : ℝ) ≤ θ / 2 * Fintype.card V := by positivity
    nlinarith
  obtain ⟨L, U, hV⟩ := hvortex V G hN hδ' hnx
  have hL : 1 ≤ L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · exfalso
      have hlast := hV.2.2.1
      rw [h0, hV.1, card_univ] at hlast
      omega
    · exact h0
  have hUL1 : U L ⊆ U 1 := hV.antitone hL le_rfl
  have hU1 : ((U 1).card : ℝ) ≤ ζ * Fintype.card V := by
    have h := (hV.2.1 0 (by omega)).2.2.2
    rw [hV.1, card_univ] at h
    have : 9 * q / 8 * (Fintype.card V : ℝ) ≤ ζ * Fintype.card V :=
      mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
    linarith
  obtain ⟨A, hAG, hAdisj, hAdeg, habs⟩ := habsorb V G hn₂ hδ hnx (U L) (U 1) hUL1 hU1
    hV.2.2.1.le
  have hAdec : HasDecomp onePart K3fam A := by
    have h0 := habs ∅ (empty_subset _) (isIntDiv_of_hasDecomp ⟨∅, by simp [IsDecomp]⟩)
    rwa [union_empty] at h0
  have hAeven := even_load_of_hasDecomp (fun e he =>
    G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (hAG he))) hAdec
  obtain ⟨EQ, hEQ, hcov, hQ⟩ := hcover V G hn₁ hdiv hδ hnx L U hV A hAG hAdisj hAdeg hAeven
  rw [← hasDecomp_K3_iff]
  exact hasDecomp_of_absorber_cover ((isIntDiv_K3_iff G).mpr hdiv) hAG
    (insideEdges_subset G (U L)) (hAdisj.mono_right (insideEdges_mono G hUL1)) habs hEQ hcov hQ

/-- **Theorem 1.8 from the two bounded-core propositions** (branch 12.5 is now the proved
`theorem146Statement_holds`). -/
theorem nash_williams_of_bounded_core (hA : CoreAbsorberSpec124) (hC : VortexCoverSpec124) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_branch124 (branch124_of_bounded_core hA hC) theorem146Statement_holds

end NashWilliams18
