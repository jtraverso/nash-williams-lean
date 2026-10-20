/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedHostMassStage176
public import PartitionedTriangleAbsorption.TypedNearPackingStage175

/-! # Type-rich physical packing from host counts and regular weights

This adapter discharges the fractional type-mass input of Stage175. The near-unit
edge loads remain a genuine input, not a consequence of divisibility.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedHostPackingStage177

open Finset TypedNibble TypedHostMassStage176 TypedNearPackingStage175

variable {V : Type} [Fintype V] [DecidableEq V] {t : ℕ}

theorem type_mass_enumeration (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (φ : Finset V → ℝ) (τ : Multiset (Fin t)) :
    (∑ i ∈ univ.filter (fun i => triType p ((copySystem p F G).tri i) = τ),
        copyWeights p F G φ i) =
      ∑ s ∈ (copies p F G).filter (fun s => triType p s = τ), φ s := by
  classical
  refine sum_bij (fun i _ => (copySystem p F G).tri i) ?_ ?_ ?_ ?_
  · intro i hi
    exact mem_filter.mpr ⟨copySystem_tri_mem p F G i, (mem_filter.mp hi).2⟩
  · intro i _ j _ hij
    exact (copySystem p F G).tri_inj hij
  · intro s hs
    obtain ⟨i, hi⟩ := copySystem_tri_surj p F G (mem_filter.mp hs).1
    refine ⟨i, mem_filter.mpr ⟨mem_univ _, ?_⟩, hi⟩
    rw [hi]
    exact (mem_filter.mp hs).2
  · intros
    rfl

theorem type_count_enumeration (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (P : Finset (Fin (copies p F G).card)) (τ : Multiset (Fin t)) :
    ((univ.filter fun i => triType p ((copySystem p F G).tri i) = τ) ∩ P).card =
      ((packedCopies p F G P).filter fun s => triType p s = τ).card := by
  classical
  have he : ((univ.filter fun i => triType p ((copySystem p F G).tri i) = τ) ∩ P).image
      (copySystem p F G).tri = (packedCopies p F G P).filter (fun s => triType p s = τ) := by
    ext s
    simp only [mem_image, mem_inter, mem_filter, mem_univ, true_and, packedCopies]
    constructor
    · rintro ⟨i, ⟨hi, hip⟩, rfl⟩
      exact ⟨⟨i, hip, rfl⟩, hi⟩
    · rintro ⟨⟨i, hip, rfl⟩, hi⟩
      exact ⟨i, ⟨hi, hip⟩, rfl⟩
  rw [← he, card_image_of_injective _ (copySystem p F G).tri_inj]

theorem typed_packing_from_host {ι : Type} [Fintype ι] [Nonempty ι]
    (α b γ η : ℝ) (hα : 0 < α) (hb : 0 < b) (hγ : 0 < γ)
    (hγ1 : γ ≤ 1 / 128) (hη : 0 < η) (hwaste : 24 * γ ^ 2 ≤ η / 2)
    (hγtypes : γ ≤ 1 / (192 * Fintype.card ι)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ α / 4 ∧ ∃ N : ℕ,
      ∀ (V : Type) [Fintype V] [DecidableEq V], N ≤ Fintype.card V →
      ∀ (t : ℕ) (p : V → Fin t) (F : Finset (Multiset (Fin t)))
        (G : SimpleGraph V) [DecidableRel G.Adj] (φ : Finset V → ℝ)
        (a₀ a₁ a₂ : ι → Fin t),
      (∀ r, ({a₀ r,a₁ r,a₂ r} : Multiset (Fin t)) ∈ F) →
      (∀ r l, l ∈ ({a₀ r,a₁ r,a₂ r} : Finset (Fin t)) →
        α * Fintype.card V ≤ ((univ.filter fun v => p v = l).card : ℝ)) →
      (∀ r l₁ l₂, (l₁, l₂) ∈ ({(a₀ r,a₁ r),(a₀ r,a₂ r),(a₁ r,a₂ r)} : Finset (Fin t × Fin t)) →
        ∀ x, p x = l₁ →
        ((univ.filter fun y => p y = l₂ ∧ ¬ G.Adj x y).card : ℝ) ≤ δ0 * Fintype.card V) →
      (∀ s, IsCopy p F G s → 1 / (b * Fintype.card V) ≤ φ s ∧ φ s ≤ b / Fintype.card V) →
      (∀ e ∈ G.edgeFinset, |(∑ s ∈ copies p F G with e ∈ triEdges s, φ s) - 1| ≤ δ0) →
      ∃ D : Finset (Finset V), ∃ Q : Finset (Sym2 V),
        D ⊆ copies p F G ∧ Q = D.biUnion triEdges ∧ Q ⊆ G.edgeFinset ∧
        IsDecomp p F Q D ∧ DegBounded (G.edgeFinset \ Q) (η * Fintype.card V) ∧
        ∀ r, γ * α ^ 3 / (432 * b) * (Fintype.card V : ℝ) ^ 2 ≤
          (D.filter fun s => triType p s = {a₀ r,a₁ r,a₂ r}).card := by
  let a := α ^ 3 / (108 * b)
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨δ, hδ, _, N, hN⟩ := packing_with_supply_near (ι := ι)
    b γ a η hb hγ hγ1 ha hη hwaste hγtypes
  let δ0 := min δ (α / 4)
  refine ⟨δ0, lt_min hδ (by positivity), min_le_right _ _, max N 1, ?_⟩
  intro V _ _ hn t p F G _ φ a₀ a₁ a₂ hτ hsize hmiss hw hload
  have hn1 : 1 ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hn' : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn1
  let S := copySystem p F G
  let J : ι → Finset (Fin (copies p F G).card) := fun r =>
    univ.filter fun i => triType p (S.tri i) = {a₀ r,a₁ r,a₂ r}
  have hmass : ∀ r, a * (Fintype.card V : ℝ) ^ 2 ≤ ∑ i ∈ J r, copyWeights p F G φ i := by
    intro r
    rw [type_mass_enumeration]
    exact fractional_type_mass p F G (a₀ r) (a₁ r) (a₂ r) (hτ r) α δ0 b hα.le
      (min_le_right _ _) hb hn1 (hsize r) (hmiss r) φ (fun s hs => (hw s hs).1)
  obtain ⟨P,hP,hdeg,hsupply⟩ := hN V ((le_max_left _ _).trans hn) (copies p F G).card
    S G.edgeFinset (copyWeights p F G φ) J
    (fun i => triEdges_subset_of_isCopy (copySystem_isCopy p F G i))
    (fun i => (div_nonneg (by norm_num) (by positivity)).trans (hw _ (copySystem_isCopy p F G i)).1)
    (fun i => (hw _ (copySystem_isCopy p F G i)).2)
    (fun e he => by rw [load_copySystem]; exact (hload e he).trans (min_le_left _ _)) hmass
  rw [edgesOf_eq_biUnion] at hdeg
  refine ⟨packedCopies p F G P, _, ?_, rfl, ?_, isDecomp_packedCopies p F G P hP, hdeg, ?_⟩
  · intro s hs
    obtain ⟨i, _, rfl⟩ := mem_image.mp hs
    exact copySystem_tri_mem p F G i
  · intro e he
    obtain ⟨s, hs, he⟩ := mem_biUnion.mp he
    obtain ⟨i, _, rfl⟩ := mem_image.mp hs
    exact triEdges_subset_of_isCopy (copySystem_isCopy p F G i) he
  · intro r
    have h := hsupply r
    rw [type_count_enumeration] at h
    convert h using 1
    dsimp [a]
    ring

end PartitionedTriangleAbsorption.TypedHostPackingStage177

