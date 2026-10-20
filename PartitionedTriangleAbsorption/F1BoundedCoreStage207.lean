/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1FractionalConfinementStage205
public import PartitionedTriangleAbsorption.UniformBoundedCoreStage104

/-! # Bounded terminal absorption from the actual F1 host hypotheses

Compatible four-root supply is derived from the per-class missing bounds.
The absorber is fixed before its future divisible subresidue. Its source
still has bounded cardinality; a degree bound alone does not suffice.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1BoundedCoreStage207

open Finset TypedApplicationLinks TypedF1AssemblyStage179 PairMoveSelectionStage85
  TypedEmbeddingSelection

theorem F1_link_admissible : ∀ i j k : Fin 4,
    TypedTransformer.Link F1 i j k → admissiblePair j i := by
  unfold TypedTransformer.Link
  decide

theorem compatible_supply_from_class_missing {V : Type} [Fintype V] [DecidableEq V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (α δ : ℝ)
    (hδ : 0 ≤ δ) (hδα : δ ≤ α / 8)
    (hsize : ∀ k, α * Fintype.card V ≤ ((univ.filter fun w => p w = k).card : ℝ))
    (hmiss : ∀ i j, admissiblePair i j → ∀ x, p x = i →
      ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ * Fintype.card V) :
    CompatibleSupply p F1 G (α / 2 * Fintype.card V) := by
  classical
  intro S hS i hi
  let bad := fun u => univ.filter fun w => p w = i ∧ ¬ G.Adj u w
  let K := univ.filter fun w => p w = i
  let T := typedNeighbours p G S i
  have hcover : K ⊆ T ∪ S.biUnion bad := by
    intro w hw
    have hp := (mem_filter.mp hw).2
    by_cases hall : ∀ u ∈ S, G.Adj u w
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hp, hall⟩)
    · push Not at hall
      obtain ⟨u, hu, huw⟩ := hall
      exact mem_union_right _ (mem_biUnion.mpr
        ⟨u, hu, mem_filter.mpr ⟨mem_univ _, hp, huw⟩⟩)
  have hbad : ∀ u ∈ S, ((bad u).card : ℝ) ≤ δ * Fintype.card V := by
    intro u hu
    obtain ⟨k, hk⟩ := hi u hu
    exact hmiss (p u) i (F1_link_admissible i (p u) k hk) u rfl
  have hc : (K.card : ℝ) ≤ T.card + ∑ u ∈ S, ((bad u).card : ℝ) := by
    exact_mod_cast (card_le_card hcover).trans
      ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))
  have hb : (∑ u ∈ S, ((bad u).card : ℝ)) ≤ 4 * δ * Fintype.card V := by
    calc
      _ ≤ ∑ _u ∈ S, δ * Fintype.card V := sum_le_sum hbad
      _ = (S.card : ℝ) * (δ * Fintype.card V) := by simp
      _ ≤ 4 * (δ * Fintype.card V) := mul_le_mul_of_nonneg_right
        (by exact_mod_cast hS) (mul_nonneg hδ (Nat.cast_nonneg _))
      _ = _ := by ring
  have hs := hsize i
  have hd := mul_le_mul_of_nonneg_right hδα (Nat.cast_nonneg (Fintype.card V))
  change α / 2 * Fintype.card V ≤ (T.card : ℝ)
  linarith

theorem uniform_F1_bounded_core_absorber (α η : ℝ) (K : ℕ)
    (hα : 0 < α) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ k, α * Fintype.card V ≤ ((univ.filter fun w => p w = k).card : ℝ)) →
      (∀ i j, admissiblePair i j → ∀ x, p x = i →
        ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ * Fintype.card V) →
      ∀ B X : Finset (Sym2 V), DegBounded B (α * Fintype.card V / 10) →
      X ⊆ G.edgeFinset → Disjoint X B → X.card ≤ K →
      ∃ A, A ⊆ G.edgeFinset ∧ Disjoint A (B ∪ X) ∧ HasDecomp p F1 A ∧
        DegBounded A (η * Fintype.card V) ∧
        ∀ L ⊆ X, IsIntDiv p F1 L → HasDecomp p F1 (A ∪ L) := by
  have hg : 0 < α / 2 := by positivity
  obtain ⟨N, hN⟩ := BoundedCoreStage104.exists_uniform_terminal_absorber
    F1 (by decide) TypedTransformer.F1_three_step K (α / 2) η hg hη
  refine ⟨α / 8, by positivity, N, ?_⟩
  intro V _ _ hn p G _ hsize hmiss B X hB hX hXB hK
  have hs := compatible_supply_from_class_missing p G α (α / 8)
    (by positivity) le_rfl hsize hmiss
  have hB' : DegBounded B (α / 2 * Fintype.card V / 5) := by
    convert hB using 1
    ring
  exact hN G p hn hs B X hB' hX hXB hK


end PartitionedTriangleAbsorption.F1BoundedCoreStage207
