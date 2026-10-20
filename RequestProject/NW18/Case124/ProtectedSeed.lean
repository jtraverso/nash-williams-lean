/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import RequestProject.NW18.Theorem26Proof

/-!
# Exact regular fractional seeds AFTER protecting resources (branch 12.4, one scale)

`protected_regular_seed`: for every sufficiently small `β > 0` there are `θ > 0`, `C ≥ 1`, `N`,
chosen before the graph and the protected set, such that whenever `n ≥ N`,
`δ(G) ≥ (3/4 - θ) n`, `G` is not `β`-extremal (literal `IsExtremal` of `NW18/Defs.lean`) and the
deleted edge set `H` has maximum degree `≤ θ n`, the graph `J = G - H` has an exact `C`-regular
fractional triangle decomposition.

Proof: Theorem 2.6 (`theorem_2_6`) at `β/2` gives `ε, C, N`; take `θ = min (ε/2) (β/4)`.
Then `δ(J) ≥ (3/4 - ε) n`, and `not_extremal_deleteEdges` with `σ = 2β` shows that `J` is not
`β/2`-extremal; the contrapositive of 2.6 applied directly to `J` gives the seed.  No weighting of
`G` is restricted to `J`.

`protected_seed_of_reserves`: the same for the reserved graph
`J = G - (A ∪ R₀ ∪ R₁ ∪ W.sym2)` (all pairs inside `W` deleted) under the elementary budget
`Δ(A) + Δ(R₀) + Δ(R₁) + |W| ≤ θ n`.
-/

namespace NashWilliams18.Case124
open Finset

theorem protected_regular_seed :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ →
      ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (H : Finset (Sym2 V)) (d : ℕ),
        N ≤ Fintype.card V →
        (3 / 4 - θ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ¬ IsExtremal β G →
        (∀ v, (H.filter (fun e => v ∈ e)).card ≤ d) →
        (d : ℝ) ≤ θ * Fintype.card V →
        ∃ w, IsRegularFracDecomp (del G H) C w := by
  obtain ⟨σ₀, hσ₀, h26⟩ := theorem_2_6
  refine ⟨σ₀, hσ₀, ?_⟩
  intro β hβ hβ₀
  obtain ⟨ε, hε, C, hC, N, hseed⟩ :=
    h26 (β / 2) (by positivity) (by linarith)
  let θ := min (ε / 2) (β / 4)
  have hθ : 0 < θ := lt_min (by positivity) (by positivity)
  have hθε : θ ≤ ε / 2 := min_le_left _ _
  have hθβ : θ ≤ β / 4 := min_le_right _ _
  refine ⟨θ, hθ, C, hC, N, ?_⟩
  intro V _ _ G _ H d hN hdeg hnx hH hd
  have hn : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hdelete : (G.minDegree : ℝ) ≤ (del G H).minDegree + d := by
    exact_mod_cast minDegree_deleteEdges_ge G H d hH
  have hres : (3 / 4 - ε) * (Fintype.card V : ℝ) ≤
      ((del G H).minDegree : ℝ) := by
    nlinarith [mul_le_mul_of_nonneg_right hθε hn]
  have hbudget : (d : ℝ) ≤ (2 * β) * Fintype.card V / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right hθβ hn]
  have hnx2 : ¬ IsExtremal ((2 * β) / 2) G := by
    rwa [mul_div_cancel_left₀ β two_ne_zero]
  have hnxres : ¬ IsExtremal (β / 2) (del G H) := by
    have := not_extremal_deleteEdges G (σ := 2 * β) (by positivity) H d hH hbudget hnx2
    rwa [show 2 * β / 4 = β / 2 by ring] at this
  by_contra hno
  exact hnxres (hseed V (del G H) hN hres hno)

section Budget

variable {V : Type*} [DecidableEq V]

/-- The edge degree of a union is at most the sum of the edge degrees. -/
lemma edeg_union_le (A B : Finset (Sym2 V)) (v : V) :
    ((A ∪ B).filter (fun e => v ∈ e)).card ≤
      (A.filter (fun e => v ∈ e)).card + (B.filter (fun e => v ∈ e)).card := by
  rw [filter_union]; exact card_union_le _ _

/-- At a vertex, the pairs inside `W` number at most `|W|`. -/
lemma edeg_sym2_le (W : Finset V) (v : V) :
    (W.sym2.filter (fun e => v ∈ e)).card ≤ W.card := by
  have hsub : W.sym2.filter (fun e => v ∈ e) ⊆ W.image (fun x => s(v, x)) := by
    intro e he
    rw [mem_filter] at he
    obtain ⟨he, hv⟩ := he
    obtain ⟨x, rfl⟩ := Sym2.mem_iff_exists.mp hv
    rw [mem_image]
    exact ⟨x, Finset.mem_sym2_iff.mp he x (Sym2.mem_mk_right _ _), rfl⟩
  exact (card_le_card hsub).trans card_image_le

end Budget

/-- **Protected seed on the reserved graph** `J = G - (A ∪ R₀ ∪ R₁ ∪ W.sym2)`: with the constants
of `protected_regular_seed`, the elementary budget `Δ(A) + Δ(R₀) + Δ(R₁) + |W| ≤ θ n` suffices for
an exact `C`-regular fractional decomposition of `J`.  The constants `θ, C, N` depend only on
`β`, never on the reserves. -/
theorem protected_seed_of_reserves :
    ∃ β₀ : ℝ, 0 < β₀ ∧ ∀ β : ℝ, 0 < β → β ≤ β₀ →
      ∃ θ : ℝ, 0 < θ ∧ ∃ C : ℝ, 1 ≤ C ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj]
        (A R₀ R₁ : Finset (Sym2 V)) (W : Finset V) (dA d₀ d₁ : ℕ),
        N ≤ Fintype.card V →
        (3 / 4 - θ) * (Fintype.card V : ℝ) ≤ (G.minDegree : ℝ) →
        ¬ IsExtremal β G →
        (∀ v, (A.filter (fun e => v ∈ e)).card ≤ dA) →
        (∀ v, (R₀.filter (fun e => v ∈ e)).card ≤ d₀) →
        (∀ v, (R₁.filter (fun e => v ∈ e)).card ≤ d₁) →
        ((dA + d₀ + d₁ + W.card : ℕ) : ℝ) ≤ θ * Fintype.card V →
        ∃ w, IsRegularFracDecomp (del G (A ∪ R₀ ∪ R₁ ∪ W.sym2)) C w := by
  obtain ⟨β₀, hβ₀, h⟩ := protected_regular_seed
  refine ⟨β₀, hβ₀, fun β hβ hββ₀ => ?_⟩
  obtain ⟨θ, hθ, C, hC, N, hs⟩ := h β hβ hββ₀
  refine ⟨θ, hθ, C, hC, N, ?_⟩
  intro V _ _ G _ A R₀ R₁ W dA d₀ d₁ hN hdeg hnx hA h₀ h₁ hb
  refine hs V G _ (dA + d₀ + d₁ + W.card) hN hdeg hnx (fun v => ?_) hb
  refine (edeg_union_le _ _ v).trans (Nat.add_le_add ?_ (edeg_sym2_le W v))
  refine (edeg_union_le _ _ v).trans (Nat.add_le_add ?_ (h₁ v))
  exact (edeg_union_le _ _ v).trans (Nat.add_le_add (hA v) (h₀ v))

end NashWilliams18.Case124
