/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingConfinementStage204
public import PartitionedTriangleAbsorption.F1UniformLinksStage193

/-! # Fractional F1 host input to an actual confined packing

Near-completeness supplies anti-edgefulness. The fractional input produces
the physical packing; neither a packing nor a good reserve is supplied.
Final absorption inside the produced reserve remains a separate obligation.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1FractionalConfinementStage205

open Finset TypedApplicationLinks TypedF1AssemblyStage179

theorem F1_compatibility : ∀ i j k : Fin 4,
    ({i, j, k} : Multiset (Fin 4)) ∈ F1 →
      admissiblePair i k ∧ admissiblePair j k := by
  decide

theorem antiEdgeful_from_class_missing {V : Type} [Fintype V]
    (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (α δ : ℝ)
    (hδ : δ ≤ α / 4)
    (hsize : ∀ k, α * Fintype.card V ≤ ((univ.filter fun w => p w = k).card : ℝ))
    (hmiss : ∀ i j, admissiblePair i j → ∀ x, p x = i →
      ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ * Fintype.card V) :
    AntiEdgeful p F1 G (α / 2) := by
  classical
  intro τ hτ i j k heq u v _ hu hv
  subst τ
  obtain ⟨hik, hjk⟩ := F1_compatibility i j k hτ
  let K := univ.filter fun w => p w = k
  let U := univ.filter fun w => p w = k ∧ ¬ G.Adj u w
  let W := univ.filter fun w => p w = k ∧ ¬ G.Adj v w
  let C := univ.filter fun w => G.Adj u w ∧ G.Adj w v ∧ p w = k
  have hcover : K ⊆ (C ∪ U) ∪ W := by
    intro w hw
    have hp := (mem_filter.mp hw).2
    by_cases h₁ : G.Adj u w
    · by_cases h₂ : G.Adj v w
      · exact mem_union_left _ (mem_union_left _
          (mem_filter.mpr ⟨mem_univ _, h₁, h₂.symm, hp⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hp, h₂⟩)
    · exact mem_union_left _ (mem_union_right _
        (mem_filter.mpr ⟨mem_univ _, hp, h₁⟩))
  have hc : K.card ≤ C.card + U.card + W.card :=
    (card_le_card hcover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  have hc' : (K.card : ℝ) ≤ C.card + U.card + W.card := by exact_mod_cast hc
  have hs : α * Fintype.card V ≤ (K.card : ℝ) := hsize k
  have hU : (U.card : ℝ) ≤ δ * Fintype.card V := hmiss i k hik u hu
  have hW : (W.card : ℝ) ≤ δ * Fintype.card V := hmiss j k hjk v hv
  have hd := mul_le_mul_of_nonneg_right hδ (Nat.cast_nonneg (Fintype.card V))
  change α / 2 * Fintype.card V ≤ (C.card : ℝ)
  linarith

theorem uniform_F1_fractional_confinement (α b η : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hb : 0 < b) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ α / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Finset V → ℝ),
      (∀ k, α * Fintype.card V ≤ ((univ.filter fun v => p v = k).card : ℝ)) →
      (∀ i j, admissiblePair i j → ∀ x, p x = i →
        ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ * Fintype.card V) →
      (∀ u v : V, G.Adj u v →
        ∃ k : Fin 4, ({p u, p v, k} : Multiset (Fin 4)) ∈ F1) →
      (∀ s, IsCopy p F1 G s →
        1 / (b * Fintype.card V) ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
      (∀ e ∈ G.edgeFinset, |TypedLoadNecessity.edgeLoad p F1 G φ e - 1| ≤ δ) →
      IsIntDiv p F1 G.edgeFinset → IsFracDiv p F1 G.edgeFinset →
      ∃ X EQ : Finset (Sym2 V), X ⊆ G.edgeFinset ∧
        DegBounded X (η * Fintype.card V) ∧ HasDecomp p F1 X ∧
        EQ ⊆ G.edgeFinset ∧ HasDecomp p F1 EQ ∧
        G.edgeFinset \ EQ ⊆ X ∧ IsIntDiv p F1 (G.edgeFinset \ EQ) ∧
        DegBounded (G.edgeFinset \ EQ) (η * Fintype.card V) ∧
        ((G.edgeFinset \ EQ).card : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2 / 2 := by
  classical
  let ρ := min (η / 2) 1
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ ≤ 1 := min_le_right _ _
  have hγ : 0 < α / 2 := by positivity
  have hγ1 : α / 2 ≤ 1 := by linarith
  obtain ⟨ζ, hζ, N₁, hN₁⟩ :=
    PackingConfinementStage204.exists_uniform_confinement 4 (α / 2) ρ
      hγ hγ1 hρ hρ1
  obtain ⟨δ, hδ, hδα, N₂, hN₂⟩ :=
    F1UniformLinksStage193.uniform_F1_packing_with_natural_links α b ζ hα hb hζ
  refine ⟨δ, hδ, hδα, max N₁ N₂, ?_⟩
  intro V _ _ hn p G _ φ hsize hmiss htype hw hload hI hfrac
  obtain ⟨D, Q, _, hQ, hD, _, hpos, _, hR⟩ :=
    hN₂ V ((le_max_right _ _).trans hn) p G φ hsize hmiss hw hload hI hfrac
  have hG := antiEdgeful_from_class_missing p G α δ hδα hsize hmiss
  obtain ⟨B, hBD, hdegree, hBX, EQ, hEQ, hdec, hconf, hdiv⟩ :=
    hN₁ V p F1 G Q D ((le_max_left _ _).trans hn) hD hQ hG hI htype hpos hR
  have hX : B.biUnion triEdges ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨s, hs, hes⟩ := mem_biUnion.mp he
    exact hQ (hD.2.2 ▸ mem_biUnion.mpr ⟨s, hBD hs, hes⟩)
  have hXdeg : DegBounded (B.biUnion triEdges) (η * Fintype.card V) := by
    intro v
    exact (hdegree v).trans (mul_le_mul_of_nonneg_right
      (show 2 * ρ ≤ η by have := min_le_left (η / 2) (1 : ℝ); dsimp [ρ]; linarith)
      (Nat.cast_nonneg _))
  have hJdeg : DegBounded (G.edgeFinset \ EQ) (η * Fintype.card V) := by
    intro v
    exact (Nat.cast_le.mpr (card_le_card (filter_subset_filter _ hconf))).trans (hXdeg v)
  refine ⟨B.biUnion triEdges, EQ, hX, hXdeg, hBX, hEQ, hdec, hconf, hdiv, hJdeg, ?_⟩
  have hc := TypedCoverDown.card_le_of_degBounded (G.edgeFinset \ EQ)
    (TypedCoverDown.not_isDiag_of_mem_edgeFinset G sdiff_subset)
    (η * Fintype.card V) hJdeg
  nlinarith


end PartitionedTriangleAbsorption.F1FractionalConfinementStage205
