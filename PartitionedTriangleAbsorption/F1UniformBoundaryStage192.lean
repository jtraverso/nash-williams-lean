/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1PairedSupplyStage191

/-! # Uniform F1 physical packing with cones and no boundary-parity holes

The extra paired-root correction is selected from the same packing. All
quantitative premises are discharged from the original host hypotheses.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1UniformBoundaryStage192

open Finset TypedApplicationLinks F1RootCountsStage182 F1UniformConeStage189
open F1BoundaryRepairStage190 F1PairedSupplyStage191 TypedF1AssemblyStage179

theorem boundary_threshold (κ : ℝ) (hκ : 0 < κ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 16 ≤ κ * n ∧ 192 ≤ κ ^ 2 * n := by
  refine ⟨max ⌈16 / κ⌉₊ ⌈192 / κ ^ 2⌉₊, ?_⟩
  intro n hn
  have h1 := (Nat.le_ceil (16 / κ)).trans (show (⌈16 / κ⌉₊ : ℝ) ≤ n by
    exact_mod_cast (le_max_left _ _).trans hn)
  have h2 := (Nat.le_ceil (192 / κ ^ 2)).trans (show (⌈192 / κ ^ 2⌉₊ : ℝ) ≤ n by
    exact_mod_cast (le_max_right _ _).trans hn)
  constructor
  · have h := mul_le_mul_of_nonneg_left h1 hκ.le
    rw [mul_div_cancel₀ _ hκ.ne'] at h
    linarith
  · have h := mul_le_mul_of_nonneg_left h2 (sq_nonneg κ)
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 hκ.ne')] at h
    linarith

theorem uniform_F1_packing_with_boundary (α b ζ : ℝ)
    (hα : 0 < α) (hb : 0 < b) (hζ : 0 < ζ) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ α / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Finset V → ℝ),
      (∀ l, α * Fintype.card V ≤ ((univ.filter fun v => p v = l).card : ℝ)) →
      (∀ i j, admissiblePair i j → ∀ x, p x = i →
        ((univ.filter fun y => p y = j ∧ ¬ G.Adj x y).card : ℝ) ≤ δ * Fintype.card V) →
      (∀ s, IsCopy p F1 G s →
        1 / (b * Fintype.card V) ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
      (∀ e ∈ G.edgeFinset,
        |TypedLoadNecessity.edgeLoad p F1 G φ e - 1| ≤ δ) →
      IsIntDiv p F1 G.edgeFinset → IsFracDiv p F1 G.edgeFinset →
      ∃ D Q, D ⊆ copies p F1 G ∧ Q ⊆ G.edgeFinset ∧ IsDecomp p F1 Q D ∧
        IsIntDiv p F1 (G.edgeFinset \ Q) ∧
        (∃ a : Multiset (Fin 4) → ℕ, edgeVec p (G.edgeFinset \ Q) =
          ∑ τ ∈ F1, (a τ : ℤ) • typeEdgeVec τ) ∧
        (∀ v, 0 ≤ surplus p (G.edgeFinset \ Q) v) ∧
        (∀ v, 0 < degVec p (G.edgeFinset \ Q) v (p v)) ∧
        DegBounded (G.edgeFinset \ Q) (ζ * Fintype.card V) := by
  classical
  let η := min (α / 8) (ζ / 2)
  let κ := min (α / 8) ζ
  have hη : 0 < η := by dsimp [η]; positivity
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hηα : η ≤ α / 8 := min_le_left _ _
  have hηζ : η ≤ ζ / 2 := min_le_right _ _
  have hκα : κ ≤ α / 8 := min_le_left _ _
  have hκζ : κ ≤ ζ := min_le_right _ _
  obtain ⟨δ, hδ, hδα, N0, hN0⟩ :=
    uniform_F1_packing_quotas_and_cones α b η hα hb hη
  obtain ⟨N1, hN1⟩ := boundary_threshold κ hκ
  refine ⟨δ, hδ, hδα, max N0 N1, ?_⟩
  intro V _ _ hn p G _ φ hsize hmiss hw hload hI hR
  have hscale := hN1 (Fintype.card V) ((le_max_right _ _).trans hn)
  obtain ⟨D, Q, hcopies, hQE, hD, _, hpos, hcones, hdeg⟩ :=
    hN0 V ((le_max_left _ _).trans hn) p G φ hsize hmiss hw hload hI hR
  have hsupply : ∀ v, κ * Fintype.card V ≤ ((pairedFamily p D v).card : ℝ) := by
    intro v
    have h := paired_supply_from_host p G Q D hD hQE v α δ η (hsize _)
      (hmiss _ _ (Or.inl rfl) v rfl) (hdeg v)
    have hcoeff : κ ≤ α - δ - η := by linarith
    have hbound := mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg (Fintype.card V))
    exact hbound.trans h
  let d := ⌊κ * Fintype.card V / 8⌋₊
  have hbudget := fun v => boundary_budget (Fintype.card V) (pairedFamily p D v).card
    κ hκ hscale.1 hscale.2 (hsupply v)
  have hd : 0 < d := Nat.floor_pos.mpr (by linarith [hscale.1])
  obtain ⟨D', Q', hsub, hQsub, hD', hI', hpos', hcones', hown, hdeg'⟩ :=
    physical_boundary_repair p G.edgeFinset Q D hD hQE hI hpos hcones d hd
      (fun v => (hbudget v).2.1)
  refine ⟨D', Q', hsub.trans hcopies, hQsub.trans hQE, hD', hI', hpos', hcones', hown, ?_⟩
  intro v
  have h : (((G.edgeFinset \ Q').filter fun e => v ∈ e).card : ℝ) ≤
      ((G.edgeFinset \ Q).filter fun e => v ∈ e).card + (2 * (d + 1) : ℕ) := by
    exact_mod_cast hdeg' v
  have hbnd := (hbudget v).2.2
  have hηn := mul_le_mul_of_nonneg_right hηζ (Nat.cast_nonneg (Fintype.card V))
  have hκn := mul_le_mul_of_nonneg_right hκζ (Nat.cast_nonneg (Fintype.card V))
  linarith [hdeg v]


end PartitionedTriangleAbsorption.F1UniformBoundaryStage192
