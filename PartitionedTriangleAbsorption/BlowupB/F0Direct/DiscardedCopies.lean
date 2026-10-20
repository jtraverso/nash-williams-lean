/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.F0Direct.UniformWeights
import PartitionedTriangleAbsorption.BlowupB.F0Direct.InverseRestriction
import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostWalkQueries

/-! # Physical count of triangles lost by removing crossing edges

A mixed triangle through a fixed surviving edge is determined by its third
vertex.  If it is present in the crossing completion and absent from the host,
at least one of its two remaining spokes is a missing crossing edge.  The
union bound therefore involves only the two endpoint crossing deficits.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset CloneSupply TypedApplicationLinks TypedNibble PackingRestriction
  HostWalkQueries F0RigidBoost
open PartitionedTriangleAbsorption.F0Direct.BalancedLinearRepair

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thirdSet_mono (p : V → Fin 2) (J H : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel H.Adj] (hJH : J ≤ H) (u v : V) :
    thirdSet p J u v ⊆ thirdSet p H u v := by
  classical
  intro w hw
  obtain ⟨hu,hv,hcol⟩ := (mem_filter.mp hw).2
  exact mem_filter.mpr ⟨mem_univ _,hJH hu,hJH hv,hcol⟩

theorem missing_third_subset (p : V → Fin 2) (J H : SimpleGraph V)
    [DecidableRel J.Adj] [DecidableRel H.Adj]
    (hInternal : ∀ u v, p u = p v → H.Adj u v → J.Adj u v) (u v : V) :
    thirdSet p H u v \ thirdSet p J u v ⊆
      (partSet p (other0 (p u)) \ partNbrs p J (other0 (p u)) u) ∪
      (partSet p (other0 (p v)) \ partNbrs p J (other0 (p v)) v) := by
  classical
  intro w hw
  obtain ⟨hwH,hwJ⟩ := mem_sdiff.mp hw
  obtain ⟨hu,hv,hcol⟩ := (mem_filter.mp hwH).2
  have hMissing (a : V) (haH : H.Adj a w) (haJ : ¬ J.Adj a w) :
      w ∈ partSet p (other0 (p a)) \ partNbrs p J (other0 (p a)) a := by
    have hne : p a ≠ p w := fun he => haJ (hInternal a w he haH)
    have hp : p w = other0 (p a) :=
      (eq_or_eq_other0 (p a) (p w)).resolve_left hne.symm
    exact mem_sdiff.mpr ⟨mem_partSet.mpr hp, fun h => haJ (mem_partNbrs.mp h).2⟩
  by_cases huJ : J.Adj u w
  · have hvJ : ¬ J.Adj v w := fun h => hwJ
      (mem_filter.mpr ⟨mem_univ _,huJ,h,hcol⟩)
    exact mem_union_right _ (hMissing v hv hvJ)
  · exact mem_union_left _ (hMissing u hu huJ)

theorem HostHyp.missing_third_card {p : V → Fin 2} {J : SimpleGraph V}
    [DecidableRel J.Adj] {α ε : ℝ} (h : HostHyp p J α ε)
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hInternal : ∀ u v, p u = p v → H.Adj u v → J.Adj u v) (u v : V) :
    ((thirdSet p H u v \ thirdSet p J u v).card : ℝ) ≤ 3 * ε * Fintype.card V := by
  classical
  have hs := card_le_card (missing_third_subset p J H hInternal u v)
  have hu := cross_missing_bound h (other0 (p u)) u (other0_ne (p u)).symm
  have hv := cross_missing_bound h (other0 (p v)) v (other0_ne (p v)).symm
  have hc := card_union_le
    (partSet p (other0 (p u)) \ partNbrs p J (other0 (p u)) u)
    (partSet p (other0 (p v)) \ partNbrs p J (other0 (p v)) v)
  have hsR := (Nat.cast_le (α := ℝ)).mpr hs
  have hcR := (Nat.cast_le (α := ℝ)).mpr hc
  push_cast at hcR
  linarith

/-- Every physical surviving edge loses at most `3 ε n` mixed copies when
crossing edges are removed and the two internal graphs are kept unchanged. -/
theorem HostHyp.discarded_copies_card {p : V → Fin 2} {J : SimpleGraph V}
    [DecidableRel J.Adj] {α ε : ℝ} (h : HostHyp p J α ε)
    (H : SimpleGraph V) [DecidableRel H.Adj] (hJH : J ≤ H)
    (hInternal : ∀ u v, p u = p v → H.Adj u v → J.Adj u v)
    (e : Sym2 V) (he : e ∈ J.edgeFinset) :
    ((edgeCopies p F0 H e \ edgeCopies p F0 J e).card : ℝ) ≤
      3 * ε * Fintype.card V := by
  classical
  induction e using Sym2.ind with
  | _ u v =>
    have huv : J.Adj u v := SimpleGraph.mem_edgeFinset.mp he
    have hI := card_sdiff_add_card_eq_card (edgeCopies_mono (p := p) (F := F0) hJH s(u,v))
    have hT := card_sdiff_add_card_eq_card (thirdSet_mono p J H hJH u v)
    have hJ : (edgeCopies p F0 J s(u,v)).card = (thirdSet p J u v).card :=
      count_copies_through_edge p J huv
    have hH : (edgeCopies p F0 H s(u,v)).card = (thirdSet p H u v).card :=
      count_copies_through_edge p H (hJH huv)
    have heq : (edgeCopies p F0 H s(u,v) \ edgeCopies p F0 J s(u,v)).card =
        (thirdSet p H u v \ thirdSet p J u v).card := by omega
    rw [heq]
    exact h.missing_third_card H hInternal u v

theorem HostHyp.balancedInverse_of_completion {p : V → Fin 2} {J : SimpleGraph V}
    [DecidableRel J.Adj] {α ε : ℝ} (h : HostHyp p J α ε) (hε : 0 ≤ ε)
    (K : ℝ) (hK : 0 ≤ K) (hn : 0 < Fintype.card V)
    (S : BalancedDemand p (CrossCompletion.complete p J) →ₗ[ℝ] (Finset V → ℝ))
    (hS : ∀ x, boundary p (CrossCompletion.complete p J) (S x) = x)
    (hNorm : ∀ x, ‖S x‖ ≤ (K / Fintype.card V) * ‖x‖)
    (hSmall : 3 * ε * K ≤ 1 / 2) : HasBoundedBalancedInverse p J (2 * K) := by
  apply InverseRestriction.hasBoundedBalancedInverse_of_supergraph p J
    (CrossCompletion.complete p J) (CrossCompletion.le_complete p J)
    K (3 * ε) hK (by positivity) hn S hS hNorm ?_ hSmall
  intro e he
  exact h.discarded_copies_card (CrossCompletion.complete p J)
    (CrossCompletion.le_complete p J)
    (fun u v hp ha => (CrossCompletion.internal p J u v hp).mp ha) e he

#print axioms HostHyp.discarded_copies_card
#print axioms HostHyp.balancedInverse_of_completion

end PartitionedTriangleAbsorption.BlowupB.F0Direct
