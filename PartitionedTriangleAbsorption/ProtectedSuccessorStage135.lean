/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ChildCapacityStage127
public import PartitionedTriangleAbsorption.AmbientChildStage131
public import PartitionedTriangleAbsorption.SpokeAwareRecutStage134

/-! # Protect a grandchild without charging its density as balance debt

The recut may avoid a dense prescribed core: this costs category capacity,
not balance. Child balance depends only on missing edges inside that child.
Finally, a protected core inherits exactly the initial missing edges, not
the accumulated damage from earlier levels. These are local successor
identities, not a construction of a complete vertex vortex.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ProtectedSuccessorStage135

open Finset AntiEdgeSelection CoverDownStage105 F3ReserveTrimStage109
open ReserveTrimStage109 SeedDrivenTrimStage114 TypedApplicationLinks
open ProtectedRecutStage126 ChildCapacityStage127 AmbientChildStage131

variable {V : Type*} [DecidableEq V]

/-- Protecting `C` inside `J` does not change the object to be balanced.
Only the available recut pools lose at most `c` edges per category. -/
theorem exists_recut_avoiding_core [Finite V] (p : V → Fin 4)
    (R J C : Finset (Sym2 V)) (hCJ : C ⊆ J)
    (b : ℝ) (m D P c : ℕ)
    (hcross : ∀ u v, s(u, v) ∈ R ∪ J → p u ≠ p v)
    (hb : ∀ k : Fin 2, |(bal p k (R ∪ J) : ℝ)| ≤ b)
    (hm : 2 * b ≤ (m : ℝ)) (hP : m < P)
    (hdeg : ∀ v, incidentLoad J v ≤ D)
    (hpool : ∀ i, P + c ≤ (pool (category p) (J \ R) i).card)
    (hcore : ∀ i, (pool (category p) C i).card ≤ c) :
    ∃ Y ⊆ J \ R, Disjoint Y C ∧ Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0 := by
  have heq : (R ∪ C) ∪ J = R ∪ J := by
    rw [union_assoc, union_eq_right.mpr hCJ]
  have hc : ∀ i, P ≤ (pool (category p) (J \ (R ∪ C)) i).card := by
    intro i
    have hs : pool (category p) ((J \ R) ∩ C) i ⊆ pool (category p) C i := by
      intro e he
      obtain ⟨hej, hei⟩ := mem_filter.mp he
      exact mem_filter.mpr ⟨(mem_inter.mp hej).2, hei⟩
    have hr : ((pool (category p) ((J \ R) ∩ C) i).card : ℝ) ≤ c := by
      exact_mod_cast (card_le_card hs).trans (hcore i)
    have hh := capacity_after_overlap (category p) (J \ R) C i (P + c) P c
      (hpool i) hr (by push_cast; rfl)
    have hdif : (J \ R) \ C = J \ (R ∪ C) := by
      ext e
      simp only [mem_sdiff, mem_union]
      tauto
    simpa only [hdif] using hh
  obtain ⟨Y, hY, hYcard, hYdeg, hbal⟩ := exists_protected_recut p (R ∪ C) J
    b m D P (by simpa only [heq] using hcross) (by simpa only [heq] using hb)
    hm hP hdeg hc
  refine ⟨Y, ?_, ?_, hYcard, hYdeg, by simpa only [heq] using hbal⟩
  · intro e he
    obtain ⟨heJ, hn⟩ := mem_sdiff.mp (hY he)
    exact mem_sdiff.mpr ⟨heJ, fun hr => hn (mem_union_left _ hr)⟩
  · apply disjoint_left.mpr
    intro e he hc'
    exact (mem_sdiff.mp (hY he)).2 (mem_union_right _ hc')

/-- The inherited global missing-degree bound is unnecessary for balance:
only missing edges *inside the child* enter this estimate. -/
theorem localized_child_balance (p : V → Fin 4) (U : Finset V)
    (E F : Finset (Sym2 V)) [DecidablePred (IsInner U)]
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E)
    (f S : ℕ) (hF : ∀ v, incidentLoad (F.filter (IsInner U)) v ≤ f)
    (hS : 0 < S) (eta : ℝ) (heta : eta ≤ 1 / 2)
    (hclass : ∀ i, (1 - eta) * S ≤ ((U.filter fun v => p v = i).card : ℝ) ∧
      ((U.filter fun v => p v = i).card : ℝ) ≤ S) (k : Fin 2) :
    |(bal p k (E.filter (IsInner U)) : ℝ)| ≤
      eta * (U.card : ℝ) ^ 2 + U.card * f := by
  apply inner_child_balance p U E (F.filter (IsInner U)) hcross ?_
    f S hF hS eta heta hclass k
  intro u hu v hv hp hn
  apply hE u hu v hv hp
  intro heF
  apply hn (mem_filter.mpr ⟨heF, ?_⟩)
  intro w hw
  rcases Sym2.mem_iff.mp hw with rfl | rfl
  · exact hu
  · exact hv

omit [DecidableEq V] in
/-- An untouched, equally sized four-class child has exactly zero balance
debt, irrespective of missing edges elsewhere in the ambient graph. -/
theorem pristine_child_balance (p : V → Fin 4) (U : Finset V)
    (E F : Finset (Sym2 V)) [DecidablePred (IsInner U)]
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E)
    (hpristine : F.filter (IsInner U) = ∅)
    (S : ℕ) (hS : 0 < S) (hclass : ∀ i, (U.filter fun v => p v = i).card = S)
    (k : Fin 2) : bal p k (E.filter (IsInner U)) = 0 := by
  classical
  have hb := localized_child_balance p U E F hcross hE 0 S
    (by intro v; simp [hpristine, incidentLoad]) hS 0 (by norm_num)
    (by intro i; simp only [hclass i]; norm_num) k
  simp only [zero_mul, Nat.cast_zero, mul_zero, add_zero] at hb
  have hz : (bal p k (E.filter (IsInner U)) : ℝ) = 0 := abs_nonpos_iff.mp hb
  exact_mod_cast hz

/-- Exact reset of inherited defects on a protected grandchild. This does
not assume the initial host was complete. -/
theorem protected_missing_reset (E0 E Pk : Finset (Sym2 V)) (K : Finset V)
    [DecidablePred (IsInner K)] (hprotect : Disjoint Pk (E.filter (IsInner K))) :
    (E0 \ (E \ Pk)).filter (IsInner K) = (E0 \ E).filter (IsInner K) := by
  apply Finset.ext
  intro e
  constructor
  · intro he
    obtain ⟨heD, heK⟩ := mem_filter.mp he
    obtain ⟨he0, hn⟩ := mem_sdiff.mp heD
    refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨he0, ?_⟩, heK⟩
    intro heE
    have heP : e ∈ Pk := by
      by_contra hp
      exact hn (mem_sdiff.mpr ⟨heE, hp⟩)
    exact disjoint_left.mp hprotect heP (mem_filter.mpr ⟨heE, heK⟩)
  · intro he
    obtain ⟨heD, heK⟩ := mem_filter.mp he
    obtain ⟨he0, hn⟩ := mem_sdiff.mp heD
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨he0, fun h => hn (mem_sdiff.mp h).1⟩, heK⟩

end PartitionedTriangleAbsorption.ProtectedSuccessorStage135
