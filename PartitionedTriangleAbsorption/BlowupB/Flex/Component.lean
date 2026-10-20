/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.Flex.Scales
public import PartitionedTriangleAbsorption.BlowupB.PaddedComponents.Split

@[expose] public section

/-!
# Componentwise universal certificates at flexible scales

`ComponentUniversalCertFlex F c k`: the statement of `ComponentUniversalCert F c k` for every
`(ω, δ, ρ)` with `FlexScales ω δ ρ n` (supply `ω n`, reserve degree `2 ρ n`, absorber degree `2 δ n`).
The rigid certificate is the special case `δ = paddedAbsDelta ω`, `ρ = paddedRho ω`
(`componentUniversalCert_of_flex`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.Flex

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.StructuralF3General
open PaddedF12 PaddedGeneral PaddedComponents

theorem FlexScales.δ_le_one {ω δ ρ n : ℝ} (h : FlexScales ω δ ρ n) : δ ≤ 1 := by
  have h1 := h.δ_le
  have h2 := h.ω_le
  have h3 := h.δ_pos
  nlinarith

/-- Componentwise universal certificate at flexible scales. -/
def ComponentUniversalCertFlex (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4) (k : Fin 4) :
    Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj] (ω δ ρ : ℝ),
    FlexScales ω δ ρ (Fintype.card V) →
    (∀ u v, G.Adj u v → ∃ k, Link F (p u) (p v) k) →
    GuardedSupply p G (fun i j => ∃ k, Link F i j k) (2 ^ 21) (ω * Fintype.card V) →
    ∀ X : Finset (Sym2 V), X ⊆ G.edgeFinset →
      DegBounded X (2 * ρ * Fintype.card V) → (∀ e ∈ X, InsideE p c k e) →
      ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧ (∀ e ∈ A, InsideE p c k e) ∧
        HasDecomp p F A ∧ DegBounded A (2 * δ * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L)

/-- The rigid certificate is the special case of the padded scales. -/
theorem componentUniversalCert_of_flex {F : Finset (Multiset (Fin 4))} {c : Fin 4 → Fin 4}
    {k : Fin 4} (h : ComponentUniversalCertFlex F c k) : ComponentUniversalCert F c k := by
  intro V _ _ p G _ ω hG hs hω hω1 hn
  exact h V p G ω (paddedAbsDelta ω) (paddedRho ω)
    (flexScales_padded ω _ hω hω1 (Nat.cast_nonneg _) hn) hG hs

/-- An empty component has the trivial flexible certificate. -/
theorem componentUniversalCertFlex_empty (F : Finset (Multiset (Fin 4))) (c : Fin 4 → Fin 4)
    (k : Fin 4) (hk : ∀ i, c i ≠ k) : ComponentUniversalCertFlex F c k := by
  intro V _ _ p G _ ω δ ρ hfl _ _ X _ _ hXin
  have hX : X = ∅ := by
    rw [eq_empty_iff_forall_notMem]
    intro e he
    have h := hXin e he
    induction e using Sym2.ind with
    | _ a b => exact hk _ ((insideE_mk p c k a b).mp h).1
  subst hX
  refine ⟨∅, empty_subset _, disjoint_empty_left _, by simp, hasDecomp_empty_set p F, ?_, ?_⟩
  · intro v
    simp only [filter_empty, card_empty, Nat.cast_zero]
    have : 0 ≤ δ := hfl.δ_pos.le
    positivity
  · intro L hL _
    have : L = ∅ := subset_empty.mp hL
    subst this
    simpa using hasDecomp_empty_set p F

end PartitionedTriangleAbsorption.BlowupB.Flex

#print axioms PartitionedTriangleAbsorption.BlowupB.Flex.componentUniversalCert_of_flex
