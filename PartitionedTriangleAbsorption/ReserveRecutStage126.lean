/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ConnectorBoundaryStage125

/-! # The quantitative interfaces needed when the child protects connectors -/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveRecutStage126

open Finset TypedApplicationLinks AntiEdgeSelection CoverDownStage105
open SelectedCoverDownStage122 ReserveQueryGeometryStage123
open F3ReserveTrimStage109 ReserveTrimStage109 ReserveAwareRecutStage120

variable {V : Type*} [DecidableEq V]

def innerEdges (T : Finset (V × V × V)) : Finset (Sym2 V) :=
  T.image fun r => s(r.2.1, r.2.2)

theorem inner_injective (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri) :
    Set.InjOn (fun r : V × V × V => s(r.2.1, r.2.2)) T := by
  intro r hr s hs he
  by_contra hn
  change s(r.2.1, r.2.2) = s(s.2.1, s.2.2) at he
  exact disjoint_left.mp (hd hr hs hn) (mem_resTri_self₃ r)
    (he.symm ▸ mem_resTri_self₃ s)

theorem inner_category_card (p : V → Fin 4) (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri) (c : Fin 3) :
    (pool (category p) (innerEdges T) c).card =
      (T.filter fun r => category p s(r.2.1, r.2.2) = c).card := by
  unfold pool innerEdges
  rw [filter_image]
  exact card_image_of_injOn ((inner_injective T hd).mono (filter_subset _ _))

theorem inner_balance_bound (p : V → Fin 4) (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (hcross : ∀ u v, s(u, v) ∈ innerEdges T → p u ≠ p v)
    (m t : ℝ)
    (hc : ∀ c, |((T.filter fun r => category p s(r.2.1, r.2.2) = c).card : ℝ) - m| ≤ t)
    (k : Fin 2) : |(bal p k (innerEdges T) : ℝ)| ≤ 2 * t := by
  rw [bal_eq_category_counts p k (innerEdges T) hcross,
    inner_category_card p T hd, inner_category_card p T hd]
  push_cast
  have h0 := abs_le.mp (hc 0)
  have hk := abs_le.mp (hc (if k = 0 then 1 else 2))
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem intersection_inner (E : Finset (Sym2 V)) (U : Finset V)
    [DecidablePred (IsInner U)]
    (T : Finset (V × V × V))
    (hT : ∀ r ∈ T, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E) :
    resEdges T ∩ (E.filter (IsInner U)) = innerEdges T := by
  classical
  ext e
  constructor
  · intro he
    obtain ⟨heR, heJ⟩ := mem_inter.mp he
    obtain ⟨r, hr, her⟩ := mem_biUnion.mp heR
    have hi := (mem_filter.mp heJ).2
    obtain ⟨hx, ha, hb, hE⟩ := hT r hr
    simp only [resTri, mem_insert, mem_singleton] at her
    rcases her with rfl | rfl | rfl
    · exact False.elim (hx (hi _ (Sym2.mem_mk_left _ _)))
    · exact False.elim (hx (hi _ (Sym2.mem_mk_left _ _)))
    · exact mem_image.mpr ⟨r, hr, rfl⟩
  · intro he
    obtain ⟨r, hr, rfl⟩ := mem_image.mp he
    obtain ⟨hx, ha, hb, hE⟩ := hT r hr
    refine mem_inter.mpr ⟨mem_biUnion.mpr ⟨r, hr, mem_resTri_self₃ r⟩,
      mem_filter.mpr ⟨hE (mem_resTri_self₃ r), ?_⟩⟩
    intro v hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ha
    · exact hb

theorem protected_union_balance_bound (p : V → Fin 4) (E : Finset (Sym2 V))
    (U : Finset V) [DecidablePred (IsInner U)] (T : Finset (V × V × V))
    (hT : ∀ r ∈ T, r.1 ∉ U ∧ r.2.1 ∈ U ∧ r.2.2 ∈ U ∧ resTri r ⊆ E)
    (hdec : HasDecomp p F3 (resEdges T))
    (k : Fin 2) (b t : ℝ)
    (hJ : |(bal p k (E.filter (IsInner U)) : ℝ)| ≤ b)
    (hI : |(bal p k (innerEdges T) : ℝ)| ≤ t) :
    |(bal p k ((E.filter (IsInner U)) ∪ resEdges T) : ℝ)| ≤ b + t := by
  classical
  rw [LateReserveStage125.overlap_charge_of_decomp p k _ _ hdec,
    inter_comm, intersection_inner E U T hT, Int.cast_sub]
  exact (abs_sub _ _).trans (add_le_add hJ hI)

theorem surviving_connectors [Finite V] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (x y z : V) (hroot : ∀ r ∈ T, r.1 = x) (Y : Finset (Sym2 V)) :
    T.card ≤ (T.filter fun r => Disjoint (connectors y z r) Y).card +
      incidentLoad Y y + incidentLoad Y z := by
  classical
  let _ := Fintype.ofFinite V
  let Z := blockedNeighbours Y y ∪ blockedNeighbours Y z
  let bad := T.filter fun r => r.1 = x ∧ (r.2.1 ∈ Z ∨ r.2.2 ∈ Z)
  have hb : bad.card ≤ incidentLoad Y y + incidentLoad Y z :=
    (card_meeting_le hd x Z).trans ((card_union_le _ _).trans
      (Nat.add_le_add (blockedNeighbours_card_le Y y) (blockedNeighbours_card_le Y z)))
  have hs : T \ bad ⊆ T.filter (fun r => Disjoint (connectors y z r) Y) := by
    intro r hr
    obtain ⟨hrT, hn⟩ := mem_sdiff.mp hr
    refine mem_filter.mpr ⟨hrT, disjoint_left.mpr ?_⟩
    intro e he heY
    simp only [connectors, mem_insert, mem_singleton] at he
    apply hn
    refine mem_filter.mpr ⟨hrT, hroot r hrT, ?_⟩
    rcases he with rfl | rfl
    · exact Or.inl (mem_union_left _ (mem_filter.mpr ⟨mem_univ _, heY⟩))
    · exact Or.inr (mem_union_right _ (mem_filter.mpr
        ⟨mem_univ _, by simpa only [Sym2.eq_swap] using heY⟩))
  have hcard := card_sdiff_add_card_eq_card (filter_subset (fun r =>
    r.1 = x ∧ (r.2.1 ∈ Z ∨ r.2.2 ∈ Z)) T)
  have hc := card_le_card hs
  change (T \ bad).card + bad.card = T.card at hcard
  omega

/-- Protecting the child except for a sparse recut suffices against every
packing outside it. The packing itself need not have small degree. -/
theorem connectors_survive_protected_child [Finite V] (T : Finset (V × V × V))
    (hd : (T : Set (V × V × V)).PairwiseDisjoint resTri)
    (x y z : V) (hroot : ∀ r ∈ T, r.1 = x)
    (J Y P : Finset (Sym2 V))
    (hJ : ∀ r ∈ T, connectors y z r ⊆ J) (hP : Disjoint P (J \ Y)) :
    T.card ≤ (T.filter fun r => Disjoint (connectors y z r) P).card +
      incidentLoad Y y + incidentLoad Y z := by
  have hsub : T.filter (fun r => Disjoint (connectors y z r) Y) ⊆
      T.filter (fun r => Disjoint (connectors y z r) P) := by
    intro r hr
    obtain ⟨hrT, hrY⟩ := mem_filter.mp hr
    refine mem_filter.mpr ⟨hrT, disjoint_left.mpr ?_⟩
    intro e he hep
    exact disjoint_left.mp hP hep (mem_sdiff.mpr
      ⟨hJ r hrT he, fun hey => disjoint_left.mp hrY he hey⟩)
  exact (surviving_connectors T hd x y z hroot Y).trans
    (Nat.add_le_add_right (Nat.add_le_add_right (card_le_card hsub) _) _)

end PartitionedTriangleAbsorption.ReserveRecutStage126
