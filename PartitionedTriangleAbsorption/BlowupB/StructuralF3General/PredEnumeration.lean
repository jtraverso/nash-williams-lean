/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.TokenLayer
public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.FiniteLibrary

/-! # Exact enumeration of a predicate refiner

This construction replaces the finite library index set by `range lib.card`.
It preserves every physical piece, the fixed remainder, the selected partitions,
and the sum of the incidence loads.  No disjointness of the whole library is
required: only the selected sublibraries are disjoint, as in `PredRefiner`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.PredRefiner

open Finset AntiEdgeSelection FiniteLibrary

variable {W κ : Type*} [DecidableEq W]
  {X0 : Finset (Sym2 W)} {Q : Finset (Sym2 W) → Prop}

noncomputable def enumerate (E : PredRefiner κ X0 Q) : PredRefiner ℕ X0 Q := by
  classical
  refine
    { lib := range E.lib.card
      P := enumPiece E.lib E.P
      R0 := E.R0
      loopP := ?_
      evenP := ?_
      subP := ?_
      disjRX := E.disjRX
      refines := ?_ }
  · intro i hi
    have hi' := mem_range.mp hi
    simpa only [enumPiece, dite_eq_left hi'] using
      E.loopP (libraryIndex E.lib ⟨i, hi'⟩) (libraryIndex_mem E.lib ⟨i, hi'⟩)
  · intro i hi
    have hi' := mem_range.mp hi
    simpa only [enumPiece, dite_eq_left hi'] using
      E.evenP (libraryIndex E.lib ⟨i, hi'⟩) (libraryIndex_mem E.lib ⟨i, hi'⟩)
  · intro i hi
    have hi' := mem_range.mp hi
    simpa only [enumPiece, dite_eq_left hi'] using
      E.subP (libraryIndex E.lib ⟨i, hi'⟩) (libraryIndex_mem E.lib ⟨i, hi'⟩)
  · intro L hLX hQ
    obtain ⟨J, hJs, hdis, hcover⟩ := E.refines L hLX hQ
    let T := (range E.lib.card).filter fun i =>
      ∃ hi : i < E.lib.card, libraryIndex E.lib ⟨i, hi⟩ ∈ J
    have hT (i : ℕ) : i ∈ T ↔
        ∃ hi : i < E.lib.card, libraryIndex E.lib ⟨i, hi⟩ ∈ J := by
      simp only [T, mem_filter, mem_range]
      exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
    refine ⟨T, filter_subset _ _, ?_, ?_⟩
    · intro i hi j hj hij
      obtain ⟨hi', hiJ⟩ := (hT i).mp hi
      obtain ⟨hj', hjJ⟩ := (hT j).mp hj
      have hne : libraryIndex E.lib ⟨i, hi'⟩ ≠ libraryIndex E.lib ⟨j, hj'⟩ := by
        intro he
        exact hij (congrArg Fin.val (libraryIndex_injective E.lib he))
      change Disjoint (enumPiece E.lib E.P i) (enumPiece E.lib E.P j)
      simpa only [enumPiece, dite_eq_left hi', dite_eq_left hj'] using hdis hiJ hjJ hne
    · rw [← hcover]
      ext e
      simp only [mem_biUnion]
      constructor
      · rintro ⟨i, hi, he⟩
        obtain ⟨hi', hiJ⟩ := (hT i).mp hi
        exact ⟨libraryIndex E.lib ⟨i, hi'⟩, hiJ, by
          simpa only [enumPiece, dite_eq_left hi'] using he⟩
      · rintro ⟨j, hj, he⟩
        let k := E.lib.equivFin ⟨j, hJs hj⟩
        have hk : libraryIndex E.lib k = j := by
          exact congrArg Subtype.val (E.lib.equivFin.symm_apply_apply ⟨j, hJs hj⟩)
        refine ⟨k.val, (hT k.val).mpr ⟨k.isLt, by simpa only [hk] using hj⟩, ?_⟩
        simpa only [enumPiece, dite_eq_left k.isLt, hk] using he

@[simp] theorem enumerate_lib (E : PredRefiner κ X0 Q) :
    E.enumerate.lib = range E.lib.card := rfl

@[simp] theorem enumerate_R0 (E : PredRefiner κ X0 Q) :
    E.enumerate.R0 = E.R0 := rfl

@[simp] theorem enumerate_card (E : PredRefiner κ X0 Q) :
    E.enumerate.lib.card = E.lib.card := card_range _

theorem enumerate_P (E : PredRefiner κ X0 Q) {i : ℕ} (hi : i < E.lib.card) :
    E.enumerate.P i = E.P (libraryIndex E.lib ⟨i, hi⟩) := by
  change enumPiece E.lib E.P i = _
  simp only [enumPiece, dite_eq_left hi]

/-- Every pointwise property of the library is preserved in both directions. -/
theorem enumerate_forall_iff (E : PredRefiner κ X0 Q)
    (H : Finset (Sym2 W) → Prop) :
    (∀ i ∈ E.enumerate.lib, H (E.enumerate.P i)) ↔ ∀ j ∈ E.lib, H (E.P j) := by
  classical
  constructor
  · intro h j hj
    let k := E.lib.equivFin ⟨j, hj⟩
    have hk : libraryIndex E.lib k = j := by
      exact congrArg Subtype.val (E.lib.equivFin.symm_apply_apply ⟨j, hj⟩)
    have hi := h k.val (mem_range.mpr k.isLt)
    rw [E.enumerate_P k.isLt, hk] at hi
    exact hi
  · intro h i hi
    have hi' : i < E.lib.card := mem_range.mp hi
    rw [E.enumerate_P hi']
    exact h _ (libraryIndex_mem E.lib ⟨i, hi'⟩)

theorem enumerate_size (E : PredRefiner κ X0 Q) (m : ℕ)
    (h : ∀ j ∈ E.lib, (E.P j).card ≤ m) :
    ∀ i ∈ E.enumerate.lib, (E.enumerate.P i).card ≤ m :=
  (E.enumerate_forall_iff (fun P => P.card ≤ m)).mpr h

theorem enumerate_incidence (E : PredRefiner κ X0 Q) (w : W) :
    ∑ i ∈ E.enumerate.lib, incidentLoad (E.enumerate.P i) w =
      ∑ j ∈ E.lib, incidentLoad (E.P j) w :=
  enumPiece_sum E.lib E.P w

#print axioms enumerate
#print axioms enumerate_forall_iff
#print axioms enumerate_incidence

end PartitionedTriangleAbsorption.StructuralF3General.PredRefiner
