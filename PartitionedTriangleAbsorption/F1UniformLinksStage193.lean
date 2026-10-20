/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1UniformBoundaryStage192
public import PartitionedTriangleAbsorption.IntegralLinkCoordinates

/-! # Natural F1 link coefficients on one uniformly produced residual

The lattice, cone and boundary conditions are verified on the same physical
residual. Natural coefficients are not simultaneous graph embeddings.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1UniformLinksStage193

open Finset TypedApplicationLinks TypedLinkCoefficients TypedDivisibilityCoordinates
open F1RootCountsStage182 F1UniformBoundaryStage192 TypedF1AssemblyStage179

theorem demand_coordinates (r : Fin 4) (x y z : ℕ) :
    demand3 r (first1 r) (second1 r) x y z r = x ∧
      demand3 r (first1 r) (second1 r) x y z (first1 r) = y ∧
      demand3 r (first1 r) (second1 r) x y z (second1 r) = z := by
  fin_cases r <;> simp [demand3, basis, first1, second1]

theorem root_natural_coefficients (r : Fin 4) (d : Fin 4 → ℤ)
    (hn : ∀ j, 0 ≤ d j) (hi : LinkLattice F1 r d)
    (hcone : d r ≤ d (first1 r) + d (second1 r)) (hown : 0 < d r) :
    Realizable F1 r d := by
  obtain ⟨x, y, z, heq, hpar⟩ := IntegralLinkCoordinates.F1_coordinates r d hn hi
  have hc := demand_coordinates r x y z
  rw [heq, hc.1, hc.2.1, hc.2.2] at hcone
  rw [heq, hc.1] at hown
  rw [heq]
  apply F1_coefficients
  · omega
  · exact hpar
  · exact Or.inl (by omega)

theorem uniform_F1_packing_with_natural_links (α b ζ : ℝ)
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
        (∀ v, Realizable F1 (p v) (degVec p (G.edgeFinset \ Q) v)) ∧
        DegBounded (G.edgeFinset \ Q) (ζ * Fintype.card V) := by
  obtain ⟨δ, hδ, hδα, N, hN⟩ := uniform_F1_packing_with_boundary α b ζ hα hb hζ
  refine ⟨δ, hδ, hδα, N, ?_⟩
  intro V _ _ hn p G _ φ hsize hmiss hw hload hI hR
  obtain ⟨D, Q, hcopies, hQ, hD, hi, ha, hcones, hown, hdeg⟩ :=
    hN V hn p G φ hsize hmiss hw hload hI hR
  refine ⟨D, Q, hcopies, hQ, hD, hi, ha, ?_, hdeg⟩
  intro v
  apply root_natural_coefficients (p v) (degVec p (G.edgeFinset \ Q) v)
    (degree_nonnegative p _ v) (hi.2 v)
  · have h := hcones v
    dsimp [surplus] at h
    linarith
  · exact hown v


end PartitionedTriangleAbsorption.F1UniformLinksStage193
