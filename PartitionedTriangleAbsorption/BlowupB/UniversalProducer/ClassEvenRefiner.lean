/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.SubsetRefiner

@[expose] public section

/-!
# The shared even refiner for families with common-link classes

`evenRefinerProducer_of_commonLinkClasses`: for a family of card-three types with
common-link classes, `EvenRefinerProducer F (Fin t × HeapIdx) 2 42 (4096 t) 2⁻²⁴` holds.
One heap refiner (`subset_refiner`) is run inside each class of vertices; the classes are
vertex-disjoint, so the remainders and libraries are edge-disjoint, and every integrally
divisible leftover splits into its class parts, each with even degrees and `3 ∣ |L_r|`
(`three_dvd_card_classEdges`).
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption PartitionedTriangleAbsorption.AntiEdgeSelection
open PartitionedTriangleAbsorption.StructuralF3General PartitionedTriangleAbsorption.OnePart
open PartitionedTriangleAbsorption.TypedTransformer

variable {t : ℕ} {V : Type} [Fintype V] [DecidableEq V]

theorem exists_mem_sym2 {α : Type*} (e : Sym2 α) : ∃ v, v ∈ e := by
  induction e using Sym2.ind with
  | _ a b => exact ⟨a, Sym2.mem_mk_left a b⟩

/-- A nonempty class has at least `ω n` vertices. -/
theorem class_card_ge (F : Finset (Multiset (Fin t))) (p : V → Fin t) (cl : Fin t → Fin t)
    (hcl : IsCommonLinkClassMap F cl) (r : Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω : ℝ) (hsup : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 2 (ω * Fintype.card V))
    {w : V} (hw : w ∈ classVerts F p cl r) :
    ω * Fintype.card V ≤ (classVerts F p cl r).card := by
  have hw' := hw
  rw [mem_classVerts, mem_classParts] at hw'
  obtain ⟨⟨a, k, hl⟩, hr⟩ := hw'
  have hn := hsup {w} (by simp) a (by
    intro x hx
    rw [mem_singleton.mp hx]
    exact ⟨k, hl⟩)
  refine hn.trans ?_
  have hsub : guardedNeighbours p G {w} a ⊆ classVerts F p cl r := by
    intro x hx
    obtain ⟨_, hxa, -⟩ := mem_filter.mp hx
    rw [mem_classVerts, mem_classParts, hxa]
    exact ⟨(activePart_of_link hl).2, (hcl.1 _ _ _ hl).symm.trans hr⟩
  exact_mod_cast card_le_card hsub

/-- The per-class refiner data. -/
theorem class_data (F : Finset (Multiset (Fin t))) (p : V → Fin t) (cl : Fin t → Fin t)
    (hcl : IsCommonLinkClassMap F cl) (r : Fin t) (G : SimpleGraph V) [DecidableRel G.Adj]
    (ω lam rho : ℝ)
    (hsup : GuardedSupply p G (fun i j => ∃ k, Link F i j k) 2 (ω * Fintype.card V))
    (hlam : 0 < lam) (h64 : 64 * lam ≤ ω) (hrho : 0 < rho) (hscale : 2 ^ 24 * rho ≤ lam ^ 2)
    (hn1 : 1 ≤ rho * Fintype.card V) (hn2 : 256 ≤ lam * Fintype.card V)
    (X : Finset (Sym2 V)) (hXG : X ⊆ G.edgeFinset) (hX : DegBounded X (2 * rho * Fintype.card V)) :
    ∃ (ind : Finset HeapIdx) (P : HeapIdx → Finset (Sym2 V)) (R : Finset (Sym2 V)),
      R ⊆ G.edgeFinset ∧ (∀ e ∈ R, ∀ v ∈ e, v ∈ classVerts F p cl r) ∧ Disjoint R X ∧
      (∀ j ∈ ind, P j ⊆ X ∪ R ∧ (∀ e ∈ P j, ¬ e.IsDiag) ∧ (∀ v, Even (incidentLoad (P j) v)) ∧
        (P j).card ≤ 42 ∧ ∀ e ∈ P j, ∀ v ∈ e, v ∈ classVerts F p cl r) ∧
      (∀ L ⊆ X, (∀ e ∈ L, ∀ v ∈ e, v ∈ classVerts F p cl r) → Even3 L →
        ∃ s ⊆ ind, (s : Set HeapIdx).PairwiseDisjoint P ∧ s.biUnion P = R ∪ L) ∧
      (∀ v, (incidentLoad R v : ℝ) ≤ 4 * lam * Fintype.card V) ∧
      (ind.card : ℝ) ≤ 1224 * rho * (Fintype.card V : ℝ) ^ 2 ∧
      ∀ v, ((∑ j ∈ ind, incidentLoad (P j) v : ℕ) : ℝ) ≤ 4096 * lam * Fintype.card V := by
  classical
  by_cases hne : (classVerts F p cl r).Nonempty
  · obtain ⟨w, hw⟩ := hne
    have hcard := class_card_ge F p cl hcl r G ω hsup hw
    have hWpos : 0 < Fintype.card (classVerts F p cl r) := by
      rw [Fintype.card_coe]; exact card_pos.mpr ⟨w, hw⟩
    have hWc : (Fintype.card (classVerts F p cl r) : ℝ) = (classVerts F p cl r).card := by
      rw [Fintype.card_coe]
    have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
    letI : DecidableRel (G.comap (Subtype.val : classVerts F p cl r → V)).Adj :=
      fun a b => inferInstanceAs (Decidable (G.Adj a.1 b.1))
    refine subset_refiner G (classVerts F p cl r) hWpos lam rho
      (ω * Fintype.card V / Fintype.card (classVerts F p cl r)) hlam hrho ?_ hscale hn1 hn2 ?_
      (class_antiEdgeful F p cl hcl r G ω hsup) X hXG hX
    · rw [hWc]
      have := mul_le_mul_of_nonneg_right h64 hn0
      linarith
    · have hWr : (0 : ℝ) < Fintype.card (classVerts F p cl r) := by exact_mod_cast hWpos
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hWr]
      have := mul_le_mul_of_nonneg_right (show 8 * lam ≤ ω by linarith) hn0
      linarith
  · rw [not_nonempty_iff_eq_empty] at hne
    refine ⟨∅, fun _ => ∅, ∅, empty_subset _, by simp, disjoint_empty_left _, by simp, ?_,
      ?_, by simp only [card_empty, Nat.cast_zero]; positivity, ?_⟩
    · intro L _ hLW _
      refine ⟨∅, empty_subset _, by simp, ?_⟩
      have hL : L = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro e he
        obtain ⟨v, hv⟩ := exists_mem_sym2 e
        have := hLW e he v hv
        rw [hne] at this
        exact absurd this (notMem_empty v)
      simp [hL]
    · intro v
      simp only [incidentLoad, filter_empty, card_empty, Nat.cast_zero]
      positivity
    · intro v
      simp only [sum_empty, Nat.cast_zero]
      positivity

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
