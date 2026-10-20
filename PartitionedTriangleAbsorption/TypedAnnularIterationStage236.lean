/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.AnnularIterationStage138

/-! # Protected iteration for every typed family, including F1

The original deterministic iteration was specialized to F3. This version
keeps the family as a parameter and reuses its residual identity and terminal
consumer. It does not assume a preselected sequence of packings. Existence
of a uniformly valid level producer and its geometric vortex remains input.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.TypedAnnularIterationStage236

open Finset AntiEdgeSelection TypedTransformer PairMoveSelectionStage85 TypedApplicationLinks

variable {V : Type*} [DecidableEq V] {t : ℕ}

/-- Damage is confined to the current annulus; the next child is untouched. -/
structure LevelState (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (R : ℕ → Finset (Sym2 V)) (cap : ℕ → ℝ) (i : ℕ)
    (D : Finset (Sym2 V)) : Prop where
  owned : D ⊆ R i
  clean : Disjoint D (R (i + 1))
  load : DegBounded D (cap i)
  divisible : IsIntDiv p F (R i \ D)

/-- Iteratively construct packings on the actual residual, retaining physical
edge-disjointness, divisibility, and the next-level damage budget. -/
theorem iterate_protected_levels (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (R : ℕ → Finset (Sym2 V)) (cap : ℕ → ℝ) (A : Finset (Sym2 V)) (L : ℕ)
    (hmono : ∀ i < L, R (i + 1) ⊆ R i)
    (hinit : LevelState p F R cap 0 A)
    (hstep : ∀ i < L, ∀ D, LevelState p F R cap i D →
      ∃ P ⊆ R i \ D, HasDecomp p F P ∧
        (R i \ D) \ P ⊆ R (i + 1) ∧ Disjoint P (R (i + 2)) ∧
        DegBounded (P ∩ R (i + 1)) (cap (i + 1))) :
    ∃ Q ⊆ R 0 \ A, HasDecomp p F Q ∧
      ∃ D, LevelState p F R cap L D ∧ (R 0 \ A) \ Q = R L \ D := by
  have hind : ∀ k ≤ L, ∃ Q ⊆ R 0 \ A, HasDecomp p F Q ∧
      ∃ D, LevelState p F R cap k D ∧ (R 0 \ A) \ Q = R k \ D := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨∅, empty_subset _, hasDecomp_empty, A, hinit, ?_⟩
      simp
    | succ k ih =>
      intro hk
      have hkL : k < L := by omega
      obtain ⟨Q, hQE, hdecQ, D, hD, hrem⟩ := ih (by omega)
      obtain ⟨P, hP, hdecP, hconf, hprotect, hload⟩ := hstep k hkL D hD
      have hPR : P ⊆ (R 0 \ A) \ Q := by rw [hrem]; exact hP
      have hQP : Disjoint Q P :=
        disjoint_left.mpr fun e hq hp => (mem_sdiff.mp (hPR hp)).2 hq
      have hnext := AnnularIterationStage138.residual_eq_child (R k) D P (R (k + 1))
        (hmono k hkL) hD.clean hconf
      have hdiv : IsIntDiv p F (R (k + 1) \ (P ∩ R (k + 1))) := by
        rw [← hnext]
        exact isIntDiv_sdiff_of_hasDecomp hD.divisible hdecP hP
      have hstate : LevelState p F R cap (k + 1) (P ∩ R (k + 1)) :=
        ⟨inter_subset_right, hprotect.mono_left inter_subset_left, hload, hdiv⟩
      refine ⟨Q ∪ P, union_subset hQE (hPR.trans sdiff_subset),
        hdecQ.union hdecP hQP, P ∩ R (k + 1), hstate, ?_⟩
      calc
        (R 0 \ A) \ (Q ∪ P) = ((R 0 \ A) \ Q) \ P := by
          ext e
          simp only [mem_sdiff, mem_union]
          tauto
        _ = (R k \ D) \ P := by rw [hrem]
        _ = R (k + 1) \ (P ∩ R (k + 1)) := hnext
  exact hind L le_rfl

/-- Close with a single absorber fixed before the iterative packing is chosen.
The terminal size is not chosen from the resulting residual. -/
theorem close_with_terminal_absorber (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (R : ℕ → Finset (Sym2 V)) (cap : ℕ → ℝ) (A : Finset (Sym2 V)) (L : ℕ)
    (hmono : ∀ i < L, R (i + 1) ⊆ R i)
    (hE : IsIntDiv p F (R 0)) (hA : HasDecomp p F A)
    (hinit : LevelState p F R cap 0 A)
    (hall : ∀ P ⊆ R L, IsIntDiv p F P → HasDecomp p F (A ∪ P))
    (hstep : ∀ i < L, ∀ D, LevelState p F R cap i D →
      ∃ P ⊆ R i \ D, HasDecomp p F P ∧
        (R i \ D) \ P ⊆ R (i + 1) ∧ Disjoint P (R (i + 2)) ∧
        DegBounded (P ∩ R (i + 1)) (cap (i + 1))) :
    HasDecomp p F (R 0) := by
  obtain ⟨Q, hQE, hQ, D, _, hrem⟩ :=
    iterate_protected_levels p F R cap A L hmono hinit hstep
  apply BoundedCoreStage104.hasDecomp_of_confined_packing
    (R 0) A (R L) Q hE hinit.owned hA hall hQ hQE
  have he : R 0 \ (A ∪ Q) = (R 0 \ A) \ Q := by
    ext e
    simp only [mem_sdiff, mem_union]
    tauto
  rw [he, hrem]
  exact sdiff_subset

/-- Construct the fixed terminal absorber in the original graph, protect
the entire first child, and then run the F1 iteration. The bound K and the
absorber threshold precede the graph and the future residual. -/
theorem f1_close_constructing_absorber (K : ℕ) (γ η : ℝ) (hγ : 0 < γ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ {V : Type} [Fintype V] [DecidableEq V]
      (G : SimpleGraph V) [DecidableRel G.Adj] (p : V → Fin 4)
      (R : ℕ → Finset (Sym2 V)) (cap : ℕ → ℝ) (L : ℕ),
      N ≤ Fintype.card V → CompatibleSupply p F1 G (γ * Fintype.card V) →
      R 0 = G.edgeFinset → (∀ i < L, R (i + 1) ⊆ R i) →
      R 1 ⊆ G.edgeFinset → R L ⊆ R 1 → (R L).card ≤ K →
      DegBounded (R 1) (γ * Fintype.card V / 5) →
      η * Fintype.card V ≤ cap 0 → IsIntDiv p F1 G.edgeFinset →
      (∀ i < L, ∀ D, LevelState p F1 R cap i D →
        ∃ P ⊆ R i \ D, HasDecomp p F1 P ∧
          (R i \ D) \ P ⊆ R (i + 1) ∧ Disjoint P (R (i + 2)) ∧
          DegBounded (P ∩ R (i + 1)) (cap (i + 1))) →
      HasDecomp p F1 G.edgeFinset := by
  obtain ⟨N, hN⟩ := BoundedCoreStage104.exists_uniform_terminal_absorber
    F1 (by decide) F1_three_step K γ η hγ hη
  refine ⟨N, ?_⟩
  intro V _ _ G _ p R cap L hn hs hzero hmono hR htail hK hload hcap hdiv hstep
  have hB : DegBounded (R 1 \ R L) (γ * Fintype.card V / 5) := by
    intro v
    have hh : ((R 1 \ R L).filter fun e => v ∈ e).card ≤
        ((R 1).filter fun e => v ∈ e).card :=
      card_le_card (filter_subset_filter _ sdiff_subset)
    exact (by exact_mod_cast hh :
      (((R 1 \ R L).filter fun e => v ∈ e).card : ℝ) ≤
        ((R 1).filter fun e => v ∈ e).card).trans (hload v)
  have hXB : Disjoint (R L) (R 1 \ R L) := by
    exact disjoint_left.mpr fun e he hf => (mem_sdiff.mp hf).2 he
  obtain ⟨A, hAG, havoid, hA, hAd, hall⟩ :=
    hN G p hn hs (R 1 \ R L) (R L) hB (htail.trans hR) hXB hK
  have hprotect : Disjoint A (R 1) := by
    have hu : (R 1 \ R L) ∪ R L = R 1 := sdiff_union_of_subset htail
    rwa [hu] at havoid
  have hAR : A ⊆ R 0 := by rwa [hzero]
  have hE : IsIntDiv p F1 (R 0) := by rwa [hzero]
  have hinit : LevelState p F1 R cap 0 A :=
    ⟨hAR, hprotect, fun v => (hAd v).trans hcap,
      isIntDiv_sdiff_of_hasDecomp hE hA hAR⟩
  rw [← hzero]
  exact close_with_terminal_absorber p F1 R cap A L hmono hE hA hinit hall hstep

end PartitionedTriangleAbsorption.TypedAnnularIterationStage236
