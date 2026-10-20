/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.SpokeReserveStage134
public import PartitionedTriangleAbsorption.OneLevelProducerStage131

/-! # Stage134: the geometric recut for `R1 ∪ R ∪ J`, not for `R ∪ J`

Stage127/131 recut the child so that `(R ∪ J) \ Y` is balanced. Once the first
spoke reserve `R1` is also withheld, Stage133 (`old_recut_debt`) shows that this
leaves exactly the debt `bal(R1)`. Here the geometric recut is redone through
`SpokeRecutStage133.recut_with_spokes`: the mutable child pools are unchanged
because `R1` consists of spokes, and the balance allowance is enlarged by the
spoke debt `b1`. The ambient form discharges the child balance input exactly
as Stage131 did.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SpokeAwareRecutStage134

open Finset CoverDownStage105 AntiEdgeSelection F3ReserveTrimStage109
open ReserveTrimStage109 ReserveRecutStage126 ChildCapacityStage127
open SeedDrivenTrimStage114 ProtectedRecutStage126 TypedApplicationLinks
open ReserveQueryGeometryStage123 AmbientChildStage131

variable {V : Type*} [DecidableEq V] [Finite V]

omit [DecidableEq V] [Finite V] in
/-- Spokes are never inner edges. -/
theorem spokes_disjoint_inner (U : Finset V) [DecidablePred (IsInner U)]
    (R1 E : Finset (Sym2 V)) (hR1 : ∀ e ∈ R1, IsSpoke U e) :
    Disjoint R1 (E.filter (IsInner U)) := by
  apply disjoint_left.mpr
  intro e he hj
  obtain ⟨a, b, ha, -, rfl⟩ := hR1 e he
  exact ha ((mem_filter.mp hj).2 a (Sym2.mem_mk_left a b))

theorem exists_spoke_geometric_recut (p : V → Fin 4) (E F R1 : Finset (Sym2 V))
    (U : Finset V) [DecidablePred (IsInner U)] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (hT : ∀ r ∈ T, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (hdec : HasDecomp p F3 (resEdges T))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (hR1E : R1 ⊆ E) (hR1 : ∀ e ∈ R1, IsSpoke U e) (hR1T : Disjoint R1 (resEdges T))
    (s b f m D P : ℕ) (z t β b1 : ℝ)
    (hsize : ∀ i, s ≤ (U.filter fun v => p v = i).card)
    (hroom : ∀ i, b + f ≤ (U.filter fun v => p v = i).card)
    (hF : ∀ v, incidentLoad F v ≤ f)
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E)
    (hc : ∀ i, |((T.filter fun r => category p s(r.2.1, r.2.2) = i).card : ℝ) - z| ≤ t)
    (hbalance : ∀ k : Fin 2, |(bal p k (E.filter (IsInner U)) : ℝ)| ≤ β)
    (hb1 : ∀ k : Fin 2, |(bal p k R1 : ℝ)| ≤ b1)
    (hcapacity : (P : ℝ) + z + t ≤ s * b)
    (hm : 2 * ((β + 2 * t) + b1) ≤ (m : ℝ)) (hP : m < P)
    (hdeg : ∀ v, incidentLoad (E.filter (IsInner U)) v ≤ D) :
    ∃ Y ⊆ (E.filter (IsInner U)) \ (R1 ∪ resEdges T), Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ k : Fin 2, bal p k (((R1 ∪ resEdges T) ∪ E.filter (IsInner U)) \ Y) = 0 := by
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
  have hdisj : Disjoint R1 (resEdges T ∪ E.filter (IsInner U)) :=
    disjoint_union_right.mpr ⟨hR1T, spokes_disjoint_inner U R1 E hR1⟩
  apply SpokeRecutStage133.recut_with_spokes p (resEdges T) R1 (E.filter (IsInner U))
    (β + 2 * t) b1 m D P hdisj ?_ ?_ hb1 hm hP hdeg hmutable
  · intro u v he
    rcases mem_union.mp he with h | hj
    · rcases mem_union.mp h with h1 | hr
      · exact hcross u v (hR1E h1)
      · exact hcross u v (hsub hr)
    · exact hcross u v (mem_filter.mp hj).1
  · intro k
    rw [union_comm]
    exact protected_union_balance_bound p E U T hT hdec k β (2 * t)
      (hbalance k) (inner_balance_bound p T hd hinner z t hc k)

/-- Ambient form: the child balance input is discharged by Stage131's
`inner_child_balance`, the degree input by `inner_load_le_card`. -/
theorem exists_spoke_ambient_recut (p : V → Fin 4) (E F R1 : Finset (Sym2 V))
    (U : Finset V) [DecidablePred (IsInner U)] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (hT : ∀ r ∈ T, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (hdec : HasDecomp p F3 (resEdges T))
    (hcross : ∀ u v, s(u, v) ∈ E → p u ≠ p v)
    (hR1E : R1 ⊆ E) (hR1 : ∀ e ∈ R1, IsSpoke U e) (hR1T : Disjoint R1 (resEdges T))
    (s b f m P S : ℕ) (z t eta b1 : ℝ)
    (hsize : ∀ i, s ≤ (U.filter fun v => p v = i).card)
    (hroom : ∀ i, b + f ≤ (U.filter fun v => p v = i).card)
    (hF : ∀ v, incidentLoad F v ≤ f)
    (hE : ∀ u ∈ U, ∀ v ∈ U, p u ≠ p v → s(u, v) ∉ F → s(u, v) ∈ E)
    (hc : ∀ i, |((T.filter fun r => category p s(r.2.1, r.2.2) = i).card : ℝ) - z| ≤ t)
    (hb1 : ∀ k : Fin 2, |(bal p k R1 : ℝ)| ≤ b1)
    (hS : 0 < S) (heta : eta ≤ 1 / 2)
    (hclass : ∀ i, (1 - eta) * S ≤ ((U.filter fun v => p v = i).card : ℝ) ∧
      ((U.filter fun v => p v = i).card : ℝ) ≤ S)
    (hcapacity : (P : ℝ) + z + t ≤ s * b)
    (hm : 2 * (((eta * (U.card : ℝ) ^ 2 + U.card * f) + 2 * t) + b1) ≤ (m : ℝ))
    (hP : m < P) :
    ∃ Y ⊆ (E.filter (IsInner U)) \ (R1 ∪ resEdges T), Y.card ≤ 2 * m ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota m U.card P) ∧
      ∀ k : Fin 2, bal p k (((R1 ∪ resEdges T) ∪ E.filter (IsInner U)) \ Y) = 0 :=
  exists_spoke_geometric_recut p E F R1 U T hd hT hdec hcross hR1E hR1 hR1T s b f m
    U.card P z t (eta * (U.card : ℝ) ^ 2 + U.card * f) b1 hsize hroom hF hE hc
    (inner_child_balance p U E F hcross hE f S hF hS eta heta hclass) hb1
    hcapacity hm hP (inner_load_le_card U E)

end PartitionedTriangleAbsorption.SpokeAwareRecutStage134
