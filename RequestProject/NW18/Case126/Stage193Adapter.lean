/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Case126.FracDivF1
public import PartitionedTriangleAbsorption.F1UniformLinksStage193

@[expose] public section

/-!
# Theorem 14.7 for `F₁`: the initial physical packing, from the ported Stage 193

This file connects the idealized `F₁`-hosts of branch (3) (`IsIdealizedT F1 ε G p`, the hosts of
`Theorem147F1Statement`) with the ported theorem
`PartitionedTriangleAbsorption.F1UniformLinksStage193.uniform_F1_packing_with_natural_links`.

The adapter uses `α = 1/8`, `b = 8` and an arbitrary `ζ > 0`; Stage 193 returns `δ` and `N`, and
we take `ε = min (δ/12) (1/100)` (Claim 14.7.1, `isRegularAlmostPacking_ideal`, needs `12 ε ≤ δ`).
The hypotheses of Stage 193 are discharged as follows.

* class sizes `≥ n/8`: `IsIdealizedT.lo` (`(1-ε) n / 4 ≥ n/8`);
* at most `δ n` non-neighbours in every admissible class: `IsIdealizedT.miss`
  (`admissiblePair i j ↔ AllowedT F1 i j`, `admissiblePair_iff_allowedT_F1`);
* weights in `[1/(8n), 8/n]` and loads within `12 ε ≤ δ` of `1`: the constant weighting
  `2/((1+3ε) n)` of `isRegularAlmostPacking_ideal`;
* fractional divisibility: `isFracDiv_F1` (Claim 14.7.2 for `F₁`).

**What the conclusion is, and what it is not.**  It is ONE physical `F₁`-packing `D` (edge set
`Q`) whose residual `R = E(G) \ Q` has maximum degree `≤ ζ n`, is integrally `F₁`-divisible, has
natural global type coefficients, and has natural `F₁`-link coefficients at every vertex
(`TypedLinkCoefficients.Realizable`: a natural combination of type degree vectors, *not* an
edge-disjoint embedding).  It is **not** an `F₁`-decomposition of `R`; turning `R` into a
decomposition (reserve/absorber) is the remaining open step of `Theorem147F1Statement`.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Stage 179's `admissiblePair` is exactly `AllowedT F1`. -/
lemma admissiblePair_iff_allowedT_F1 (i j : Fin 4) :
    TypedF1AssemblyStage179.admissiblePair i j ↔ AllowedT F1 i j := by
  rw [allowedT_F1_iff]; revert i j; decide

omit [DecidableEq V] in
/-- Non-neighbours of `x` in the class `V_j`: `|V_j| - deg_j(x)`. -/
lemma card_nonNbr_add_degT (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4) (x : V)
    (j : Fin 4) :
    (univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card + degT G p x j = (clsT p j).card := by
  classical
  have h := card_filter_add_card_filter_not (s := clsT p j) (fun y => G.Adj x y)
  have e1 : (clsT p j).filter (fun y => G.Adj x y) =
      univ.filter (fun w => G.Adj x w ∧ p w = j) := by
    ext w; simp [clsT, and_comm]
  have e2 : (clsT p j).filter (fun y => ¬ G.Adj x y) =
      univ.filter (fun y => p y = j ∧ ¬ G.Adj x y) := by
    ext w; simp [clsT]
  rw [e1, e2] at h
  unfold degT; omega

/-- **The initial physical packing of Theorem 14.7 for `F₁`** (Stage 193 applied to the
idealized hosts of branch (3)).  For every `ζ > 0` there are `ε ∈ (0, 1/100]` and `n₀` such that
every integrally `F₁`-divisible `ε`-balanced `ε`-nearly-complete `F₁`-blowup `G` on `n ≥ n₀`
vertices contains a physical `F₁`-packing `D` with edge set `Q ⊆ E(G)` whose residual
`E(G) \ Q` is integrally `F₁`-divisible, has natural global type coefficients and natural link
coefficients at every vertex, and has maximum degree at most `ζ n`.  This is not a
decomposition of the residual. -/
theorem F1_ideal_packing_with_natural_links (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 / 100 ∧ ∃ n₀ : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
        (G : SimpleGraph V) [DecidableRel G.Adj], n₀ ≤ Fintype.card V →
        IsIntDiv p F1 G.edgeFinset → IsIdealizedT F1 ε G p →
        ∃ D Q, D ⊆ copies p F1 G ∧ Q ⊆ G.edgeFinset ∧ IsDecomp p F1 Q D ∧
          IsIntDiv p F1 (G.edgeFinset \ Q) ∧
          (∃ a : Multiset (Fin 4) → ℕ, edgeVec p (G.edgeFinset \ Q) =
            ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ) ∧
          (∀ v, TypedLinkCoefficients.Realizable F1 (p v)
            (degVec p (G.edgeFinset \ Q) v)) ∧
          DegBounded (G.edgeFinset \ Q) (ζ * Fintype.card V) := by
  obtain ⟨δ, hδ, -, N, hN⟩ :=
    F1UniformLinksStage193.uniform_F1_packing_with_natural_links (1 / 8) 8 ζ
      (by norm_num) (by norm_num) hζ
  refine ⟨min (δ / 12) (1 / 100), lt_min (by positivity) (by norm_num), min_le_right _ _,
    max N 1, ?_⟩
  intro V _ _ p G _ hn hint hid
  set ε := min (δ / 12) (1 / 100) with hεdef
  have hε0 : 0 ≤ ε := le_min (by positivity) (by norm_num)
  have hε1 : ε ≤ 1 / 100 := min_le_right _ _
  have hε12 : 12 * ε ≤ δ := by have := min_le_left (δ / 12) (1 / 100); linarith
  have hnpos : 0 < Fintype.card V := lt_of_lt_of_le (by omega) hn
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hnpos
  have hreg := isRegularAlmostPacking_ideal twoThirds_F1 hε0 hε1 (le_refl (12 * ε)) hnpos hid
  apply hN V (le_trans (le_max_left _ _) hn) p G (fun _ => 2 / ((1 + 3 * ε) * Fintype.card V))
  · intro l
    have h := hid.lo l
    have e : ((univ.filter fun v => p v = l).card : ℝ) = ((clsT p l).card : ℝ) := rfl
    rw [e]
    nlinarith
  · intro i j hij x hx
    have hal : AllowedT F1 (p x) j := by
      rw [hx]; exact (admissiblePair_iff_allowedT_F1 i j).mp hij
    have h1 := hid.miss hal
    have h2 := card_nonNbr_add_degT G p x j
    have h2' : ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) +
        (degT G p x j : ℝ) = ((clsT p j).card : ℝ) := by exact_mod_cast h2
    have h3 : ε * (Fintype.card V : ℝ) ≤ δ * Fintype.card V := by
      apply mul_le_mul_of_nonneg_right _ hnR.le; linarith
    linarith
  · intro s hs
    obtain ⟨h1, h2⟩ := hreg.1 s hs
    exact ⟨by simpa using h1, by
      refine h2.trans ?_
      gcongr⟩
  · intro e he
    obtain ⟨h1, h2⟩ := hreg.2 e he
    have e1 : TypedLoadNecessity.edgeLoad p F1 G
        (fun _ => 2 / ((1 + 3 * ε) * Fintype.card V)) e =
        ∑ s ∈ copies p F1 G with e ∈ triEdges s, 2 / ((1 + 3 * ε) * Fintype.card V) := rfl
    rw [e1, abs_le]
    constructor <;> linarith
  · exact hint
  · exact isFracDiv_F1 hε0 hε1 hnpos hid hint

end NashWilliams18
