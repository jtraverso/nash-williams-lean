/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ChildCapacityStage127

/-! # Recut from physical child capacity and balanced reserve counts

The mutable capacity premise of Stage126 is discharged from colour-class
sizes and sparse forbidden edges. Balance, degree and numerical hierarchy
budgets are still explicit; no full vortex construction is asserted here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.GeometricRecutStage127

open Finset CoverDownStage105 AntiEdgeSelection F3ReserveTrimStage109
open ReserveTrimStage109 ReserveRecutStage126 ChildCapacityStage127
open SeedDrivenTrimStage114 ProtectedRecutStage126 TypedApplicationLinks
open ReserveQueryGeometryStage123

variable {V : Type*} [DecidableEq V] [Finite V]

theorem exists_geometric_recut (p : V → Fin 4) (E F : Finset (Sym2 V))
    (U : Finset V) [DecidablePred (IsInner U)] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (hT : ∀ r ∈ T, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (hdec : HasDecomp p F3 (resEdges T))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (s b f m D P : ℕ) (z t β : ℝ)
    (hsize : ∀ i, s ≤ (U.filter fun v => p v = i).card)
    (hroom : ∀ i, b + f ≤ (U.filter fun v => p v = i).card)
    (hF : ∀ v, incidentLoad F v ≤ f)
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E)
    (hc : ∀ i, |((T.filter fun r => category p s(r.2.1, r.2.2) = i).card : ℝ) - z| ≤ t)
    (hbalance : ∀ k : Fin 2, |(bal p k (E.filter (IsInner U)) : ℝ)| ≤ β)
    (hcapacity : (P : ℝ) + z + t ≤ s * b)
    (hm : 2 * (β + 2 * t) ≤ (m : ℝ)) (hP : m < P)
    (hdeg : ∀ v, incidentLoad (E.filter (IsInner U)) v ≤ D) :
    ∃ Y ⊆ (E.filter (IsInner U)) \ resEdges T, Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ k : Fin 2, bal p k ((resEdges T ∪ E.filter (IsInner U)) \ Y) = 0 := by
  have hsub : resEdges T ⊆ E := by
    intro e he
    obtain ⟨r, hr, her⟩ := mem_biUnion.mp he
    exact (hT r hr).2.2.2 her
  have hinner : ∀ u v, s(u, v) ∈ innerEdges T → p u ≠ p v := by
    intro u v he
    rw [← intersection_inner E U T hT] at he
    exact hcross u v (hsub (mem_inter.mp he).1)
  have hcap := all_category_capacity p U (E.filter (IsInner U)) F s b f
    hsize hroom hF (by
      intro u hu v hv hne hnF
      refine mem_filter.mpr ⟨hE u hu v hv hne hnF, ?_⟩
      intro w hw
      rcases Sym2.mem_iff.mp hw with rfl | rfl
      · exact hu
      · exact hv)
  have hmutable := mutable_child_capacity p E U T hd hT (s * b) P z t hcap hc
    (by exact_mod_cast hcapacity)
  apply exists_protected_recut p (resEdges T) (E.filter (IsInner U))
    (β + 2 * t) m D P ?_ ?_ hm hP hdeg hmutable
  · intro u v he
    rcases mem_union.mp he with hr | hj
    · exact hcross u v (hsub hr)
    · exact hcross u v (mem_filter.mp hj).1
  · intro k
    rw [union_comm]
    exact protected_union_balance_bound p E U T hT hdec k β (2 * t)
      (hbalance k) (inner_balance_bound p T hd hinner z t hc k)

/-- A numerical loss budget gives supply above a prescribed threshold.
It does not assume the later packing is sparse. -/
theorem query_supply_after_recut (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (x y z : V) (hroot : ∀ r ∈ T, r.1 = x)
    (J Y P : Finset (Sym2 V)) (q : ℕ) (a target : ℝ)
    (hJ : ∀ r ∈ T, connectors y z r ⊆ J) (hP : Disjoint P (J \ Y))
    (hdeg : ∀ v, incidentLoad Y v ≤ 3 * q)
    (hrich : a / 192 < (T.card : ℝ))
    (hbudget : target + 6 * q ≤ a / 192) :
    target < ((T.filter fun r => Disjoint (connectors y z r) P).card : ℝ) := by
  have hs := connectors_survive_protected_child T hd x y z hroot J Y P hJ hP
  have hl : T.card ≤ (T.filter fun r => Disjoint (connectors y z r) P).card + 6 * q := by
    have hy := hdeg y
    have hz := hdeg z
    omega
  have hlR : (T.card : ℝ) ≤
      (T.filter fun r => Disjoint (connectors y z r) P).card + 6 * q := by
    exact_mod_cast hl
  linarith

end PartitionedTriangleAbsorption.GeometricRecutStage127
