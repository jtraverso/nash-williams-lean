/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveRecutStage126

/-! # Recut a protected child without assuming disjointness from the reserve

The overlap is allowed and charged. The child category capacity and the
degree budget remain explicit; they must be paid by the global hierarchy.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ProtectedRecutStage126

open Finset CoverDownStage105 AntiEdgeSelection F3ReserveTrimStage109
open ReserveTrimStage109 SeedDrivenTrimStage114
open ReserveAwareRecutStage120 TypedApplicationLinks

variable {V : Type*} [DecidableEq V]

omit [DecidableEq V] in
theorem category_gap_of_balance (p : V → Fin 4) (E : Finset (Sym2 V))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (b : ℝ) (m : ℕ) (hb : ∀ k : Fin 2, |(bal p k E : ℝ)| ≤ b)
    (hm : 2 * b ≤ (m : ℝ)) :
    ∀ i j, (pool (category p) E i).card ≤ (pool (category p) E j).card + m := by
  have h0 := hb 0
  have h1 := hb 1
  rw [bal_eq_category_counts p 0 E hcross] at h0
  rw [bal_eq_category_counts p 1 E hcross] at h1
  norm_num only [ite_true, Fin.isValue, zero_ne_one, one_ne_zero, ite_false,
    Int.cast_sub, Int.cast_natCast] at h0 h1
  have hpos : 0 ≤ b := (abs_nonneg _).trans h0
  obtain ⟨h0l, h0u⟩ := abs_le.mp h0
  obtain ⟨h1l, h1u⟩ := abs_le.mp h1
  intro i j
  have hr : ((pool (category p) E i).card : ℝ) ≤
      (pool (category p) E j).card + m := by
    fin_cases i <;> fin_cases j <;> norm_num at * <;> linarith
  exact_mod_cast hr

theorem exists_protected_recut [Finite V] (p : V → Fin 4)
    (R J : Finset (Sym2 V)) (b : ℝ) (m D P : ℕ)
    (hcross : ∀ u v, s(u, v) ∈ R ∪ J → p u ≠ p v)
    (hb : ∀ k : Fin 2, |(bal p k (R ∪ J) : ℝ)| ≤ b)
    (hm : 2 * b ≤ (m : ℝ)) (hP : m < P)
    (hdeg : ∀ v, incidentLoad J v ≤ D)
    (hpool : ∀ i, P ≤ (pool (category p) (J \ R) i).card) :
    ∃ Y ⊆ J \ R, Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0 := by
  have hloop : ∀ e ∈ J, ¬ e.IsDiag := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      intro hd
      exact hcross u v (mem_union_right R he)
        (congrArg p (Sym2.mk_isDiag_iff.mp hd))
  obtain ⟨Y, hY, hc, hd, heq⟩ := SmallTrimStage118.exists_small_trim
    (category p) R J m D P hP hloop hdeg
    (category_gap_of_balance p (R ∪ J) hcross b m hb hm) hpool
  refine ⟨Y, hY, hc, hd, ?_⟩
  intro k
  rw [bal_eq_category_counts p k _
    (fun u v he => hcross u v (mem_sdiff.mp he).1), heq, heq, sub_self]

/-- The protected reserve may overlap the child. A recut outside the reserve
and its disjoint physical pre-cover still give the correct balanced nibble
host; no disjointness between R and J is silently assumed. -/
theorem actual_host_balanced_overlap (p : V → Fin 4)
    (E R J Y S : Finset (Sym2 V)) (hY : Y ⊆ J \ R)
    (hS : Disjoint S (R ∪ J)) (hsub : S ∪ (R ∪ J) ⊆ E)
    (hE : ∀ k : Fin 2, bal p k E = 0) (hdec : HasDecomp p F3 (Y ∪ S))
    (hbal : ∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0) :
    ∀ k : Fin 2, bal p k (E \ ((Y ∪ S) ∪ (R ∪ (J \ Y)))) = 0 := by
  have hYJ : Y ⊆ J := hY.trans sdiff_subset
  have hYU : Y ⊆ R ∪ J := hYJ.trans subset_union_right
  have hYS : Disjoint Y S := (hS.mono_right hYU).symm
  have heq : (Y ∪ S) ∪ (R ∪ (J \ Y)) = S ∪ (R ∪ J) := by
    ext e
    simp only [mem_union, mem_sdiff]
    have := @hYJ e
    tauto
  intro k
  have hzero := bal_zero_of_hasDecomp p k hdec
  rw [bal_union p k hYS] at hzero
  have hr := hbal k
  rw [bal_sdiff p k hYU] at hr
  rw [heq, bal_sdiff p k hsub, bal_union p k hS, hE k]
  omega

end PartitionedTriangleAbsorption.ProtectedRecutStage126
