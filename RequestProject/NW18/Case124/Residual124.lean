/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.NW18.Main124Branch
public import RequestProject.NW18.Case124.SignedCertificateHosts
public import PartitionedTriangleAbsorption.ReturnedAssembly

@[expose] public section

/-!
# Branch 12.4: the exact remaining propositions, with explicit quantifier order

The robust-absorption route for the non-extremal branch needs two existence statements on the
actual hosts (`δ(G) ≥ 3n/4`, not `β`-extremal).  Neither is proved here.

* `ReserveCoverSpec124` (**prechosen reserve; nibble and cover-down**): a sparse reserve `X` is
  chosen first, depending only on `G`; then, for **every** sparse absorber `A` edge-disjoint from
  `X` (of density up to `C·γ`, `C` given in advance), a triangle-decomposable `EQ ⊆ E(G) \ A`
  covers every edge outside `A ∪ X`.
* `OmniAbsorberSpec124` (**absorber for a given reserve**): for every sparse `X` there is a sparse
  `A`, disjoint from `X`, such that `A ∪ L` is triangle-decomposable for **every** divisible
  `L ⊆ X` (the absorber is fixed before the residual `L` is known).

`branch124_of_specs` proves the exact branch statement `Branch124Statement` from the two, by the
deterministic assembly `hasDecomp_of_absorber_cover`; `nash_williams_of_specs` then gives the
conclusion of Theorem 1.8 together with `Theorem146Statement`.

The proved input for `OmniAbsorberSpec124` is `ParityFill.robust_signed_certificate`: every
divisible edge set of the residual `(G - F)[U]` (Stage 268 budgets) has a physical signed
triangle certificate inside `(G - F)[U]` of cost `≤ 16741 |E|`.  Turning these signed
certificates into nonnegative, edge-disjoint absorber gadgets is the missing step.
-/

namespace NashWilliams18

open Finset PartitionedTriangleAbsorption

/-- **Prechosen reserve with nibble and cover-down on the 12.4 hosts** (not proved). -/
def ReserveCoverSpec124 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 → ∀ C : ℝ, 0 < C → ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
      3 * Fintype.card V ≤ 4 * G.minDegree → ¬ IsExtremal β G →
      ∃ X ⊆ G.edgeFinset, DegBounded X (γ * Fintype.card V) ∧
        ∀ A ⊆ G.edgeFinset, Disjoint A X → DegBounded A (C * γ * Fintype.card V) →
          ∃ EQ : Finset (Sym2 V), EQ ⊆ G.edgeFinset \ A ∧ G.edgeFinset \ (A ∪ X) ⊆ EQ ∧
            HasDecomp onePart K3fam EQ

/-- **Omni-absorber for a given sparse reserve on the 12.4 hosts** (not proved). -/
def OmniAbsorberSpec124 : Prop :=
  ∀ β : ℝ, 0 < β → β ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → 3 * Fintype.card V ≤ 4 * G.minDegree → ¬ IsExtremal β G →
      ∀ X ⊆ G.edgeFinset, DegBounded X (γ * Fintype.card V) →
        ∃ A ⊆ G.edgeFinset, Disjoint A X ∧ DegBounded A (C * γ * Fintype.card V) ∧
          ∀ L ⊆ X, IsIntDiv onePart K3fam L → HasDecomp onePart K3fam (A ∪ L)

/-- **Branch 12.4 from the two remaining propositions** (deterministic assembly). -/
theorem branch124_of_specs (hA : OmniAbsorberSpec124) (hR : ReserveCoverSpec124) :
    Branch124Statement := by
  refine ⟨1, one_pos, fun β hβ hβ1 => ?_⟩
  obtain ⟨C, hC, γ₁, hγ₁, hA'⟩ := hA β hβ hβ1
  obtain ⟨γ₂, hγ₂, hR'⟩ := hR β hβ hβ1 C hC
  set γ := min γ₁ γ₂
  have hγ : 0 < γ := lt_min hγ₁ hγ₂
  obtain ⟨n₁, hA''⟩ := hA' γ hγ (min_le_left _ _)
  obtain ⟨n₂, hR''⟩ := hR' γ hγ (min_le_right _ _)
  refine ⟨max n₁ n₂, fun V _ _ G _ hn hdiv hδ hnx => ?_⟩
  obtain ⟨X, hXG, hXdeg, hcover⟩ := hR'' V G (le_trans (le_max_right _ _) hn) hdiv hδ hnx
  obtain ⟨A, hAG, hAX, hAdeg, habs⟩ :=
    hA'' V G (le_trans (le_max_left _ _) hn) hδ hnx X hXG hXdeg
  obtain ⟨EQ, hEQ, hcov, hQ⟩ := hcover A hAG hAX hAdeg
  rw [← hasDecomp_K3_iff]
  exact hasDecomp_of_absorber_cover ((isIntDiv_K3_iff G).mpr hdiv) hAG hXG hAX habs hEQ hcov hQ

/-- **Theorem 1.8 from the two remaining propositions of branch 12.4 and Theorem 14.6.** -/
theorem nash_williams_of_specs (hA : OmniAbsorberSpec124) (hR : ReserveCoverSpec124)
    (h146 : Theorem146Statement) :
    ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      N ≤ Fintype.card V → NashWilliams.IsTriangleDivisible G →
        3 * Fintype.card V ≤ 4 * G.minDegree → NashWilliams.HasTriangleDecomposition G :=
  nash_williams_of_branch124 (branch124_of_specs hA hR) h146

end NashWilliams18
