/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Transformer
public import PartitionedTriangleAbsorption.AntiEdgeFamily

/-! # From a supplied refiner to a universal typed absorber

The private absorbers are fixed before the leftover is selected. Only a subset
of the fixed piece library changes. This proves the composition step, not the
existence of a bounded refiner or its physical embedding in a host graph.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.RefinerAssembly

open Finset

variable {V I : Type*} [DecidableEq V] {t : ℕ}
variable {p : V → Fin t} {F : Finset (Multiset (Fin t))}

theorem empty_hasDecomp : HasDecomp p F (∅ : Finset (Sym2 V)) := by
  exact ⟨∅, by simp [IsDecomp]⟩

theorem empty_isIntDiv : IsIntDiv p F (∅ : Finset (Sym2 V)) := by
  constructor
  · refine ⟨fun _ => 0, ?_⟩
    simp [edgeVec]
  · intro v
    refine ⟨fun _ => 0, ?_⟩
    simp [degVec]

theorem hasDecomp_biUnion (s : Finset I) (E : I → Finset (Sym2 V))
    (hdec : ∀ i ∈ s, HasDecomp p F (E i))
    (hdis : (s : Set I).PairwiseDisjoint E) :
    HasDecomp p F (s.biUnion E) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (empty_hasDecomp (p := p) (F := F))
  | insert a s ha ih =>
    rw [biUnion_insert]
    refine HasDecomp.union (hdec a (mem_insert_self _ _))
      (ih (fun i hi => hdec i (mem_insert_of_mem hi))
        (hdis.subset (by simp))) ?_
    rw [disjoint_biUnion_right]
    intro i hi
    exact hdis (by simp) (by simp [hi]) (fun h => ha (h ▸ hi))

/-- Activate precisely the pieces selected by a refiner certificate. -/
def activeBlock [DecidableEq I] (s : Finset I)
    (A B : I → Finset (Sym2 V)) (i : I) : Finset (Sym2 V) :=
  if i ∈ s then A i ∪ B i else A i

theorem activeBlock_biUnion [DecidableEq I] (indices s : Finset I)
    (hsub : s ⊆ indices) (A B : I → Finset (Sym2 V)) :
    indices.biUnion (activeBlock s A B) = indices.biUnion A ∪ s.biUnion B := by
  ext e
  constructor
  · intro he
    obtain ⟨i, hi, he⟩ := mem_biUnion.mp he
    by_cases his : i ∈ s
    · rw [activeBlock, ite_eq_left his] at he
      rcases mem_union.mp he with he | he
      · exact mem_union_left _ (mem_biUnion.mpr ⟨i, hi, he⟩)
      · exact mem_union_right _ (mem_biUnion.mpr ⟨i, his, he⟩)
    · rw [activeBlock, ite_eq_right his] at he
      exact mem_union_left _ (mem_biUnion.mpr ⟨i, hi, he⟩)
  · intro he
    rcases mem_union.mp he with he | he
    · obtain ⟨i, hi, he⟩ := mem_biUnion.mp he
      refine mem_biUnion.mpr ⟨i, hi, ?_⟩
      by_cases his : i ∈ s
      · simp only [activeBlock, ite_eq_left his]
        exact mem_union_left _ he
      · simpa only [activeBlock, ite_eq_right his] using he
    · obtain ⟨i, his, he⟩ := mem_biUnion.mp he
      refine mem_biUnion.mpr ⟨i, hsub his, ?_⟩
      simp only [activeBlock, ite_eq_left his]
      exact mem_union_right _ he

/-- The exact decomposition for one selected, edge-disjoint piece partition. -/
theorem selected_assembly (indices s : Finset I)
    (hsub : s ⊆ indices) (J : Finset (Sym2 V)) (A B : I → Finset (Sym2 V))
    (hA : ∀ i ∈ indices, HasDecomp p F (A i))
    (hAB : ∀ i ∈ indices, HasDecomp p F (A i ∪ B i))
    (hprivate : (indices : Set I).PairwiseDisjoint A)
    (havoid : ∀ i ∈ indices, Disjoint (A i) J)
    (hpieces : ∀ i ∈ indices, B i ⊆ J)
    (hselected : (s : Set I).PairwiseDisjoint B) :
    HasDecomp p F (indices.biUnion A ∪ s.biUnion B) := by
  classical
  rw [← activeBlock_biUnion indices s hsub A B]
  apply hasDecomp_biUnion
  · intro i hi
    by_cases his : i ∈ s
    · simpa only [activeBlock, ite_eq_left his] using hAB i hi
    · simpa only [activeBlock, ite_eq_right his] using hA i hi
  · intro i hi j hj hij
    change Disjoint (activeBlock s A B i) (activeBlock s A B j)
    have hAA := hprivate hi hj hij
    have hAiBj := (havoid i hi).mono_right (hpieces j hj)
    have hBiAj := ((havoid j hj).mono_right (hpieces i hi)).symm
    by_cases his : i ∈ s <;> by_cases hjs : j ∈ s
    · simp only [activeBlock, ite_eq_left his, ite_eq_left hjs]
      exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hAA, hAiBj⟩,
        disjoint_union_right.mpr ⟨hBiAj, hselected his hjs hij⟩⟩
    · simp only [activeBlock, ite_eq_left his, ite_eq_right hjs]
      exact disjoint_union_left.mpr ⟨hAA, hBiAj⟩
    · simp only [activeBlock, ite_eq_right his, ite_eq_left hjs]
      exact disjoint_union_right.mpr ⟨hAA, hAiBj⟩
    · simpa only [activeBlock, ite_eq_right his, ite_eq_right hjs] using hAA

/-- A finite piece library refines every divisible leftover of the fixed reserve.
Different leftovers may select overlapping library pieces: they are never
activated simultaneously. Existence and quantitative bounds are separate goals. -/
def RefinesReserve (indices : Finset I)
    (B : I → Finset (Sym2 V)) (X R : Finset (Sym2 V)) : Prop :=
  ∀ L ⊆ X, IsIntDiv p F L → ∃ s ⊆ indices,
    (s : Set I).PairwiseDisjoint B ∧ s.biUnion B = R ∪ L

/-- One fixed absorber, with the correct universal quantifier over leftovers. -/
theorem universal_of_refiner
    (indices : Finset I) (A B : I → Finset (Sym2 V)) (X R : Finset (Sym2 V))
    (hRX : Disjoint R X)
    (href : RefinesReserve (p := p) (F := F) indices B X R)
    (hA : ∀ i ∈ indices, HasDecomp p F (A i))
    (hAB : ∀ i ∈ indices, HasDecomp p F (A i ∪ B i))
    (hprivate : (indices : Set I).PairwiseDisjoint A)
    (havoid : ∀ i ∈ indices, Disjoint (A i) (X ∪ R))
    (hpieces : ∀ i ∈ indices, B i ⊆ X ∪ R) :
    Disjoint (R ∪ indices.biUnion A) X ∧
      HasDecomp p F (R ∪ indices.biUnion A) ∧
      ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F ((R ∪ indices.biUnion A) ∪ L) := by
  classical
  have hall : ∀ L ⊆ X, IsIntDiv p F L →
      HasDecomp p F ((R ∪ indices.biUnion A) ∪ L) := by
    intro L hLX hdiv
    obtain ⟨s, hsub, hdis, hcover⟩ := href L hLX hdiv
    have h := selected_assembly indices s hsub (X ∪ R) A B
      hA hAB hprivate havoid hpieces hdis
    rw [hcover] at h
    simpa only [union_assoc, union_left_comm, union_comm] using h
  refine ⟨disjoint_union_left.mpr ⟨hRX, ?_⟩, ?_, hall⟩
  · rw [disjoint_biUnion_left]
    intro i hi
    exact (havoid i hi).mono_right subset_union_left
  · simpa using hall ∅ (empty_subset X) (empty_isIntDiv (p := p) (F := F))

/-- Degree control is paid through local private incidence, not by the number
of possible residuals. The private sets need not be disjoint for this bound. -/
theorem absorber_degree_bound (indices : Finset I) (A : I → Finset (Sym2 V))
    (R : Finset (Sym2 V)) (d b : ℝ) (hR : DegBounded R d)
    (hload : ∀ x, ((∑ i ∈ indices, AntiEdgeSelection.incidentLoad (A i) x : ℕ) : ℝ) ≤ b) :
    DegBounded (R ∪ indices.biUnion A) (d + b) := by
  intro x
  have hcount : ((indices.biUnion A).filter (fun e => x ∈ e)).card ≤
      ∑ i ∈ indices, AntiEdgeSelection.incidentLoad (A i) x := by
    rw [filter_biUnion]
    exact card_biUnion_le
  have htotal := card_union_le (R.filter (fun e => x ∈ e))
    ((indices.biUnion A).filter (fun e => x ∈ e))
  have hnat : ((R ∪ indices.biUnion A).filter (fun e => x ∈ e)).card ≤
      (R.filter (fun e => x ∈ e)).card +
        ∑ i ∈ indices, AntiEdgeSelection.incidentLoad (A i) x := by
    rw [filter_union]
    exact htotal.trans (Nat.add_le_add_left hcount _)
  have hreal : (((R ∪ indices.biUnion A).filter (fun e => x ∈ e)).card : ℝ) ≤
      ((R.filter (fun e => x ∈ e)).card : ℝ) +
        ((∑ i ∈ indices, AntiEdgeSelection.incidentLoad (A i) x : ℕ) : ℝ) := by
    exact_mod_cast hnat
  linarith [hR x, hload x]

end PartitionedTriangleAbsorption.RefinerAssembly
