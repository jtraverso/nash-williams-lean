/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PackingTransitionStage137
public import PartitionedTriangleAbsorption.TerminalCoreClosureStage104

/-! # Finite iteration of protected physical levels

A level producer must work for every admissible current damage set. This file
iterates that producer, without assuming a preselected sequence of packings,
and joins the resulting physical packing to a terminal absorber. The geometric
vortex and the uniform quantitative hypotheses of the producer remain inputs.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.AnnularIterationStage138

open Finset AntiEdgeSelection TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

/-- The dynamic state retains only the most recent annular damage. -/
structure LevelState (p : V → Fin 4) (R : ℕ → Finset (Sym2 V))
    (cap : ℕ → ℝ) (i : ℕ) (D : Finset (Sym2 V)) : Prop where
  owned : D ⊆ R i
  clean : Disjoint D (R (i + 1))
  load : DegBounded D (cap i)
  divisible : IsIntDiv p F3 (R i \ D)

/-- A clean child and confinement identify the next host exactly. -/
theorem residual_eq_child (E D P C : Finset (Sym2 V))
    (hCE : C ⊆ E) (hclean : Disjoint D C) (hconf : (E \ D) \ P ⊆ C) :
    (E \ D) \ P = C \ (P ∩ C) := by
  ext e
  constructor
  · intro he
    have hc := hconf he
    exact mem_sdiff.mpr ⟨hc, fun hp => (mem_sdiff.mp he).2 (mem_inter.mp hp).1⟩
  · intro he
    obtain ⟨hc, hn⟩ := mem_sdiff.mp he
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hCE hc, ?_⟩, ?_⟩
    · exact fun hd => disjoint_left.mp hclean hd hc
    · exact fun hp => hn (mem_inter.mpr ⟨hp, hc⟩)

/-- Construct the accumulated packing by repeatedly invoking a level producer.
The state and each next packing are chosen in order on the actual remaining set. -/
theorem iterate_protected_levels (p : V → Fin 4) (R : ℕ → Finset (Sym2 V))
    (cap : ℕ → ℝ) (A : Finset (Sym2 V)) (L : ℕ)
    (hmono : ∀ i < L, R (i + 1) ⊆ R i)
    (hinit : LevelState p R cap 0 A)
    (hstep : ∀ i < L, ∀ D, LevelState p R cap i D →
      ∃ P ⊆ R i \ D, HasDecomp p F3 P ∧
        (R i \ D) \ P ⊆ R (i + 1) ∧ Disjoint P (R (i + 2)) ∧
        DegBounded (P ∩ R (i + 1)) (cap (i + 1))) :
    ∃ Q ⊆ R 0 \ A, HasDecomp p F3 Q ∧
      ∃ D, LevelState p R cap L D ∧ (R 0 \ A) \ Q = R L \ D := by
  have hind : ∀ k ≤ L, ∃ Q ⊆ R 0 \ A, HasDecomp p F3 Q ∧
      ∃ D, LevelState p R cap k D ∧ (R 0 \ A) \ Q = R k \ D := by
    intro k
    induction k with
    | zero =>
      intro _
      refine ⟨∅, empty_subset _, ?_, A, hinit, ?_⟩
      · exact hasDecomp_empty
      · simp
    | succ k ih =>
      intro hk
      have hkL : k < L := by omega
      obtain ⟨Q, hQE, hdecQ, D, hD, hrem⟩ := ih (by omega)
      obtain ⟨P, hP, hdecP, hconf, hprotect, hload⟩ := hstep k hkL D hD
      have hPR : P ⊆ (R 0 \ A) \ Q := by rw [hrem]; exact hP
      have hQP : Disjoint Q P := by
        exact disjoint_left.mpr fun e hq hp => (mem_sdiff.mp (hPR hp)).2 hq
      have hnext := residual_eq_child (R k) D P (R (k + 1))
        (hmono k hkL) hD.clean hconf
      have hdiv : IsIntDiv p F3 (R (k + 1) \ (P ∩ R (k + 1))) := by
        rw [← hnext]
        exact isIntDiv_sdiff_of_hasDecomp hD.divisible hdecP hP
      have hstate : LevelState p R cap (k + 1) (P ∩ R (k + 1)) :=
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

/-- The iterated producer leaves exactly the residual absorbed by the fixed A.
This closes the deterministic assembly, not the uniform existence of its input vortex. -/
theorem close_with_terminal_absorber (p : V → Fin 4)
    (R : ℕ → Finset (Sym2 V)) (cap : ℕ → ℝ) (A : Finset (Sym2 V)) (L : ℕ)
    (hmono : ∀ i < L, R (i + 1) ⊆ R i)
    (hE : IsIntDiv p F3 (R 0)) (hA : HasDecomp p F3 A)
    (hinit : LevelState p R cap 0 A)
    (hall : ∀ P ⊆ R L, IsIntDiv p F3 P → HasDecomp p F3 (A ∪ P))
    (hstep : ∀ i < L, ∀ D, LevelState p R cap i D →
      ∃ P ⊆ R i \ D, HasDecomp p F3 P ∧
        (R i \ D) \ P ⊆ R (i + 1) ∧ Disjoint P (R (i + 2)) ∧
        DegBounded (P ∩ R (i + 1)) (cap (i + 1))) :
    HasDecomp p F3 (R 0) := by
  obtain ⟨Q, hQE, hQ, D, -, hrem⟩ :=
    iterate_protected_levels p R cap A L hmono hinit hstep
  apply BoundedCoreStage104.hasDecomp_of_confined_packing
    (R 0) A (R L) Q hE hinit.owned hA hall hQ hQE
  have he : R 0 \ (A ∪ Q) = (R 0 \ A) \ Q := by
    ext e
    simp only [mem_sdiff, mem_union]
    tauto
  rw [he, hrem]
  exact sdiff_subset

end PartitionedTriangleAbsorption.AnnularIterationStage138
