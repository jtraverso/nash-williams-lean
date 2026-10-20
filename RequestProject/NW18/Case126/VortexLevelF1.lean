/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Case126.IdealPeelingF1

/-!
# Theorem 14.7 for `F₁`, vortex route: the regime of the crossing cover, and the first open step

* `crossing_cover_regime` (proved): whenever the hypotheses of
  `CrossingCover.F1_crossing_cover` hold with crossing stars inside `U`, then
  `16 |X| γ₁ + 3 |X| ≤ |U| γ₁`.  In particular a nonempty apex set satisfies `16 |X| < |U|`.
  So the proved crossing cover (and hence `F1_peeling_level`) only works in the *peeling regime*
  `|W \ U| ≪ |U|`; a vortex level has `|U| = β |W|` with `β` small, i.e. `|W \ U| ≫ |U|`.
  This is a statement about the proof method (double counting of the crossing load), recorded so
  that the next step is not attempted with the same budget.

* `F1VortexCoverDown` (**NOT proved**, a `def` only): the precise first unproved sublemma of the
  vortex route — one self-similar cover-down level in the vortex regime, with explicit
  quantifiers and constants.  It is stated with respect to a fixed host `G` (typicality never
  degrades) and a current graph `H ⊆ G[W]` whose damage (edges of `G[W]` missing from `H`) has
  maximum degree `≤ ζ |W|` and never lies inside `U`.  The conclusion leaves `H \ D` inside `U`,
  never uses an edge inside the next set `U'`, and damages `G[U]` by maximum degree `≤ ζ |U|`, so
  the hypotheses reproduce themselves on `(U, U', U'')`.
-/

namespace NashWilliams18.CrossingCover

open Finset PartitionedTriangleAbsorption LinkPairing
open PartitionedTriangleAbsorption.TypedApplicationLinks (F1)

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- **The regime of the crossing cover** (proved).  Under the load and margin hypotheses of
`F1_crossing_cover`, with every crossing star inside `U`, `16 |X| γ₁ + 3 |X| ≤ |U| γ₁`. -/
theorem crossing_cover_regime (p : V → Fin 4) (X U : Finset V) (N : V → Finset V)
    (γ₀ γ₁ : ℕ) (hNU : ∀ x ∈ X, N x ⊆ U) (hload : ∀ y, crossLoad X N y ≤ γ₁)
    (hmarg : ∀ x ∈ X, LinkMargins p x (N x) (γ₀ + γ₁)) :
    16 * X.card * γ₁ + 3 * X.card ≤ U.card * γ₁ := by
  classical
  -- double counting of the crossing load
  have hdc : ∑ x ∈ X, (U.filter fun y => y ∈ N x).card = ∑ y ∈ U, crossLoad X N y :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (fun x y => y ∈ N x)
  have hstar : ∀ x ∈ X, 16 * γ₁ + 3 ≤ (U.filter fun y => y ∈ N x).card := by
    intro x hx
    obtain ⟨m1, m2, m3, -, -⟩ := hmarg x hx
    obtain ⟨hc1, hc2, h12⟩ := partner_ne (p x)
    have hfilt : (U.filter fun y => y ∈ N x) = N x := by
      ext y; simp only [mem_filter, and_iff_right_iff_imp]; exact fun h => hNU x hx h
    rw [hfilt]
    have hdc' : ∀ a b : Fin 4, a ≠ b → Disjoint ((N x).filter fun y => p y = a)
        ((N x).filter fun y => p y = b) := by
      intro a b hab
      rw [disjoint_left]
      intro u hu hu'
      exact hab ((mem_filter.mp hu).2.symm.trans (mem_filter.mp hu').2)
    have hsub : ((N x).filter fun y => p y = p x) ∪ ((N x).filter fun y => p y = partner1 (p x))
        ∪ ((N x).filter fun y => p y = partner2 (p x)) ⊆ N x := by
      intro y hy
      simp only [mem_union, mem_filter] at hy
      rcases hy with (h | h) | h <;> exact h.1
    have := card_le_card hsub
    rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hdc' _ _ hc2, hdc' _ _ h12⟩),
      card_union_of_disjoint (hdc' _ _ hc1)] at this
    omega
  have h1 : X.card * (16 * γ₁ + 3) ≤ ∑ x ∈ X, (U.filter fun y => y ∈ N x).card := by
    have := card_nsmul_le_sum X (fun x => (U.filter fun y => y ∈ N x).card) _ hstar
    simpa [smul_eq_mul] using this
  have h2 : ∑ y ∈ U, crossLoad X N y ≤ U.card * γ₁ := by
    have := sum_le_card_nsmul U (fun y => crossLoad X N y) γ₁ (fun y _ => hload y)
    simpa [smul_eq_mul] using this
  nlinarith

/-- **Open obligation (NOT proved): one self-similar `F₁` cover-down level in the vortex regime.**

For constants `β` (level ratio), `ξ` (typicality of the fixed host `G`) and `ζ` (damage budget)
there is `m₀` such that: for every host `G` with `F₁`-allowed edges, sets `U' ⊆ U ⊆ W` with
`|W| ≥ m₀`, `β|W|/2 ≤ |U| ≤ β|W|`, `β|U|/2 ≤ |U'| ≤ β|U|`, every class occupying at least a fifth
of each of `W, U, U'`, every vertex of `W` missing at most `ξ|W|` (resp. `ξ|U|`) vertices of `W`
(resp. `U`) of each allowed class, and every vertex of `U` missing at most `ξ|U'|` vertices of `U'`
of each allowed class; and for every integrally `F₁`-divisible `H ⊆ G` with all edges inside `W`,
whose damage `G[W] \ H` has maximum degree `≤ ζ|W|` and no edge inside `U`:
there is an `F₁`-decomposable `D ⊆ E(H)` such that every edge of `H` outside `D` lies inside `U`,
no edge of `D` lies inside `U'`, and the edges of `D` inside `U` have maximum degree `≤ ζ|U|`.

(The proved `F1_peeling_level` gives the analogous statement when `|W \ U| ≤ |U|/16`;
`crossing_cover_regime` shows that its crossing-load budget cannot reach `|U| = β|W|`.) -/
def F1VortexCoverDown (β ξ ζ : ℝ) : Prop :=
  ∃ m₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj] (W U U' : Finset V),
    U' ⊆ U → U ⊆ W → m₀ ≤ W.card →
    β * W.card / 2 ≤ U.card → (U.card : ℝ) ≤ β * W.card →
    β * U.card / 2 ≤ U'.card → (U'.card : ℝ) ≤ β * U.card →
    (∀ u v, G.Adj u v → AllowedT F1 (p u) (p v)) →
    (∀ j : Fin 4, (W.card : ℝ) / 5 ≤ (W.filter fun z => p z = j).card ∧
      (U.card : ℝ) / 5 ≤ (U.filter fun z => p z = j).card ∧
      (U'.card : ℝ) / 5 ≤ (U'.filter fun z => p z = j).card) →
    (∀ v ∈ W, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((W.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * W.card ∧
      ((U.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * U.card) →
    (∀ v ∈ U, ∀ j : Fin 4, AllowedT F1 (p v) j →
      ((U'.filter fun z => p z = j ∧ ¬ G.Adj v z).card : ℝ) ≤ ξ * U'.card) →
    IsIntDiv p F1 H.edgeFinset → H ≤ G → (∀ u v, H.Adj u v → u ∈ W) →
    (∀ u ∈ U, ∀ v ∈ U, G.Adj u v → H.Adj u v) →
    (∀ u ∈ W, ((W.filter fun v => G.Adj u v ∧ ¬ H.Adj u v).card : ℝ) ≤ ζ * W.card) →
    ∃ D ⊆ H.edgeFinset, HasDecomp p F1 D ∧
      (∀ e ∈ H.edgeFinset, e ∉ D → ∀ v ∈ e, v ∈ U) ∧
      (∀ e ∈ D, ¬ ∀ v ∈ e, v ∈ U') ∧
      ∀ v, (((D.filter fun e => ∀ w ∈ e, w ∈ U).filter fun e => v ∈ e).card : ℝ) ≤ ζ * U.card

end NashWilliams18.CrossingCover
