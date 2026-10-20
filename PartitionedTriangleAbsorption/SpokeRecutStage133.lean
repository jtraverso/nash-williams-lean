/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ProtectedRecutStage126

/-! # Charge the first spoke reserve BEFORE choosing the recut

The withheld set is R1 union R union J, not merely R union J. A spoke
reserve outside R union J leaves the mutable child pools unchanged, but
its balance discrepancy must be included. Its construction remains open.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SpokeRecutStage133

open Finset AntiEdgeSelection CoverDownStage105 TypedApplicationLinks
open F3ReserveTrimStage109 ReserveTrimStage109 SeedDrivenTrimStage114
open ReserveAwareRecutStage120 ProtectedRecutStage126

variable {V : Type*} [DecidableEq V]

/-- An old balanced recut need not balance the host with the spokes withheld. -/
theorem old_recut_debt (p : V → Fin 4) (R R1 J Y : Finset (Sym2 V))
    (hd : Disjoint R1 (R ∪ J)) (hY : Y ⊆ J)
    (hz : ∀ k : Fin 2, bal p k ((R ∪ J) \ Y) = 0) :
    ∀ k : Fin 2, bal p k (((R1 ∪ R) ∪ J) \ Y) = bal p k R1 := by
  have hRY : Disjoint R1 Y := hd.mono_right (hY.trans subset_union_right)
  have heq : ((R1 ∪ R) ∪ J) \ Y = R1 ∪ ((R ∪ J) \ Y) := by
    ext e
    have hdis : e ∈ R1 → e ∉ Y := fun h => disjoint_left.mp hRY h
    simp only [mem_sdiff, mem_union]
    tauto
  intro k
  rw [heq, bal_union p k (hd.mono_right sdiff_subset), hz k, add_zero]

/-- Adding the spoke balance allowance repairs the combined recut target.
The supply in J minus R is still enough since R1 has no child edges. -/
theorem recut_with_spokes [Finite V] (p : V → Fin 4)
    (R R1 J : Finset (Sym2 V)) (b b1 : ℝ) (m D P : ℕ)
    (hd : Disjoint R1 (R ∪ J))
    (hcross : ∀ u v, s(u, v) ∈ (R1 ∪ R) ∪ J → p u ≠ p v)
    (hb : ∀ k : Fin 2, |(bal p k (R ∪ J) : ℝ)| ≤ b)
    (hb1 : ∀ k : Fin 2, |(bal p k R1 : ℝ)| ≤ b1)
    (hm : 2 * (b + b1) ≤ (m : ℝ)) (hP : m < P)
    (hdeg : ∀ v, incidentLoad J v ≤ D)
    (hpool : ∀ i, P ≤ (pool (category p) (J \ R) i).card) :
    ∃ Y ⊆ J \ (R1 ∪ R), Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ k : Fin 2, bal p k (((R1 ∪ R) ∪ J) \ Y) = 0 := by
  have hpools : J \ (R1 ∪ R) = J \ R := by
    ext e
    have hn : e ∈ J → e ∉ R1 := fun hj hr =>
      disjoint_left.mp hd hr (mem_union_right _ hj)
    simp only [mem_sdiff, mem_union]
    tauto
  apply exists_protected_recut p (R1 ∪ R) J (b + b1) m D P hcross ?_ hm hP hdeg
    (by simpa only [hpools] using hpool)
  intro k
  rw [union_assoc, bal_union p k hd, Int.cast_add]
  calc
    |(bal p k R1 : ℝ) + bal p k (R ∪ J)| ≤
        |(bal p k R1 : ℝ)| + |(bal p k (R ∪ J) : ℝ)| := abs_add_le _ _
    _ ≤ b + b1 := by linarith [hb k, hb1 k]

end PartitionedTriangleAbsorption.SpokeRecutStage133
