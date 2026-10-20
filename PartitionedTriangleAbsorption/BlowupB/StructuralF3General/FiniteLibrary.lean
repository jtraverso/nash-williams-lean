/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.StructuralF3General.PrivateFamily
public import Mathlib.Algebra.BigOperators.Fin

/-! # Exact enumeration of a fixed finite refiner library

Selections, physical pieces, and summed incidence are transported unchanged.
This module is generic in the type family and in the finite index set.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StructuralF3General.FiniteLibrary

open Finset AntiEdgeSelection PrivateFamily

variable {V I : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

noncomputable def libraryIndex (s : Finset I) (i : Fin s.card) : I :=
  (s.equivFin.symm i : I)

theorem libraryIndex_mem (s : Finset I) (i : Fin s.card) : libraryIndex s i ∈ s :=
  (s.equivFin.symm i).2

theorem libraryIndex_injective (s : Finset I) : Function.Injective (libraryIndex s) :=
  fun _ _ h => s.equivFin.symm.injective (Subtype.ext h)

noncomputable def enumPiece (s : Finset I) (B : I → Finset (Sym2 V))
    (i : ℕ) : Finset (Sym2 V) :=
  if hi : i < s.card then B (libraryIndex s ⟨i, hi⟩) else ∅

omit [Fintype V] in
theorem enumPiece_sum (s : Finset I) (B : I → Finset (Sym2 V)) (v : V) :
    ∑ i ∈ range s.card, incidentLoad (enumPiece s B i) v =
      ∑ j ∈ s, incidentLoad (B j) v := by
  classical
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ i : Fin s.card, incidentLoad (enumPiece s B i.val) v =
        ∑ i : Fin s.card, incidentLoad (B (libraryIndex s i)) v := by
      apply sum_congr rfl
      intro i _
      simp [enumPiece, i.isLt]
    _ = ∑ j ∈ s, incidentLoad (B j) v := by
      rw [← sum_coe_sort s]
      exact Equiv.sum_comp s.equivFin.symm (fun j => incidentLoad (B j) v)

omit [Fintype V] in
theorem enumPiece_refines (p : V → Fin t) (F : Finset (Multiset (Fin t))) (s : Finset I)
    (B : I → Finset (Sym2 V)) (X R : Finset (Sym2 V))
    (href : RefinerAssembly.RefinesReserve (p := p) (F := F) s B X R) :
    RefinerAssembly.RefinesReserve (p := p) (F := F) (range s.card)
      (enumPiece s B) X R := by
  classical
  intro L hLX hdiv
  obtain ⟨J, hJs, hdis, hcover⟩ := href L hLX hdiv
  let T := (range s.card).filter fun i =>
    ∃ hi : i < s.card, libraryIndex s ⟨i, hi⟩ ∈ J
  have hT (i : ℕ) : i ∈ T ↔ ∃ hi : i < s.card, libraryIndex s ⟨i, hi⟩ ∈ J := by
    simp only [T, mem_filter, mem_range]
    exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩
  refine ⟨T, filter_subset _ _, ?_, ?_⟩
  · intro i hi j hj hij
    obtain ⟨hi', hiJ⟩ := (hT i).mp hi
    obtain ⟨hj', hjJ⟩ := (hT j).mp hj
    have hne : libraryIndex s ⟨i, hi'⟩ ≠ libraryIndex s ⟨j, hj'⟩ := by
      intro he
      exact hij (congrArg Fin.val (libraryIndex_injective s he))
    change Disjoint (enumPiece s B i) (enumPiece s B j)
    simpa only [enumPiece, dite_eq_left hi', dite_eq_left hj'] using hdis hiJ hjJ hne
  · rw [← hcover]
    ext e
    simp only [mem_biUnion]
    constructor
    · rintro ⟨i, hi, he⟩
      obtain ⟨hi', hiJ⟩ := (hT i).mp hi
      exact ⟨libraryIndex s ⟨i, hi'⟩, hiJ, by
        simpa only [enumPiece, dite_eq_left hi'] using he⟩
    · rintro ⟨j, hj, he⟩
      let k := s.equivFin ⟨j, hJs hj⟩
      have hk : libraryIndex s k = j := by
        exact congrArg Subtype.val (s.equivFin.symm_apply_apply ⟨j, hJs hj⟩)
      refine ⟨k.val, (hT k.val).mpr ⟨k.isLt, by simpa only [hk] using hj⟩, ?_⟩
      simpa only [enumPiece, dite_eq_left k.isLt, hk] using he

theorem card_le_order_mul_degree (E : Finset (Sym2 V)) (d : ℝ)
    (hE : DegBounded E d) : (E.card : ℝ) ≤ Fintype.card V * d := by
  classical
  have hcover : E ⊆ univ.biUnion (fun v : V => E.filter fun e => v ∈ e) := by
    intro e he
    induction e using Sym2.ind with
    | _ a b => exact mem_biUnion.mpr ⟨a, mem_univ _, mem_filter.mpr ⟨he, by simp⟩⟩
  have hc : E.card ≤ ∑ v : V, incidentLoad E v :=
    (card_le_card hcover).trans card_biUnion_le
  have hcR : (E.card : ℝ) ≤ ∑ v : V, (incidentLoad E v : ℝ) := by
    exact_mod_cast hc
  apply hcR.trans
  calc
    ∑ v : V, (incidentLoad E v : ℝ) ≤ ∑ _v : V, d := sum_le_sum fun v _ => hE v
    _ = Fintype.card V * d := by rw [sum_const, card_univ, nsmul_eq_mul]

theorem universal_from_finite_library (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) [DecidableRel G.Adj] (m C : ℕ) (T D Λ ρ a : ℝ)
    (hstep : PrivateStep p F G m C T D a)
    (X R : Finset (Sym2 V)) (hRX : Disjoint R X)
    (hXG : X ⊆ G.edgeFinset) (hRG : R ⊆ G.edgeFinset)
    (hledger : DegBounded (X ∪ R) ρ) (hD : max ρ (T + C) + C * Λ ≤ D)
    (s : Finset I) (B : I → Finset (Sym2 V))
    (href : RefinerAssembly.RefinesReserve (p := p) (F := F) s B X R)
    (hpieces : ∀ i ∈ s, B i ⊆ X ∪ R)
    (hm : ∀ i ∈ s, (B i).card ≤ m) (hdiv : ∀ i ∈ s, IsIntDiv p F (B i))
    (hload : ∀ v, ((∑ i ∈ s, incidentLoad (B i) v : ℕ) : ℝ) ≤ Λ)
    (hcount : 4 * (((X ∪ R).card : ℝ) + s.card * C) ≤ T * a) :
    ∃ A : Finset (Sym2 V), A ⊆ G.edgeFinset ∧ Disjoint A X ∧
      HasDecomp p F A ∧ DegBounded A D ∧
      ∀ L ⊆ X, IsIntDiv p F L → HasDecomp p F (A ∪ L) := by
  have hpieces' : ∀ i < s.card, enumPiece s B i ⊆ X ∪ R := by
    intro i hi
    simpa only [enumPiece, dite_eq_left hi] using
      hpieces (libraryIndex s ⟨i, hi⟩) (libraryIndex_mem s ⟨i, hi⟩)
  have hm' : ∀ i < s.card, (enumPiece s B i).card ≤ m := by
    intro i hi
    simpa only [enumPiece, dite_eq_left hi] using
      hm (libraryIndex s ⟨i, hi⟩) (libraryIndex_mem s ⟨i, hi⟩)
  have hdiv' : ∀ i < s.card, IsIntDiv p F (enumPiece s B i) := by
    intro i hi
    simpa only [enumPiece, dite_eq_left hi] using
      hdiv (libraryIndex s ⟨i, hi⟩) (libraryIndex_mem s ⟨i, hi⟩)
  have hload' : ∀ v, (PrivateFamily.rootLoad (enumPiece s B) s.card v : ℝ) ≤ Λ := by
    intro v
    have h := PrivateFamily.rootLoad_le_incidence_sum (enumPiece s B) s.card v
    rw [enumPiece_sum] at h
    have hr : (PrivateFamily.rootLoad (enumPiece s B) s.card v : ℝ) ≤
        ((∑ i ∈ s, incidentLoad (B i) v : ℕ) : ℝ) := by exact_mod_cast h
    exact hr.trans (hload v)
  exact PrivateFamily.universal_from_library p F G m C T D Λ ρ a hstep X R hRX hRG
    hledger hD s.card (enumPiece s B) (enumPiece_refines p F s B X R href)
    hpieces' (fun i hi => (hpieces' i hi).trans (union_subset hXG hRG)) hm' hdiv'
    hload' hcount

#print axioms enumPiece_refines
#print axioms universal_from_finite_library

end PartitionedTriangleAbsorption.StructuralF3General.FiniteLibrary
