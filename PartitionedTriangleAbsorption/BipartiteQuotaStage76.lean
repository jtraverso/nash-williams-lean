/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedCoverDownConsumer
public import PartitionedTriangleAbsorption.AntiEdgeSelection

/-! # Physical bipartite requests with a degree quota

The cardinality and congestion budgets are explicit. No edge selector or good
outcome is supplied: each new unordered pair is selected away from the blocked
edges and from saturated endpoints. This is a deterministic ingredient of the
neutral-reserve producer, not that producer itself.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BipartiteQuotaStage76

open Finset AntiEdgeSelection

variable {V : Type*} [Finite V] [DecidableEq V]

def Joins (L R : Finset V) (Y : Finset (Sym2 V)) : Prop :=
  ∀ e ∈ Y, ∃ u ∈ L, ∃ v ∈ R, e = s(u, v)

omit [Finite V] [DecidableEq V] in
theorem joins_loopless {L R : Finset V} {Y : Finset (Sym2 V)}
    (hLR : Disjoint L R) (hY : Joins L R Y) : ∀ e ∈ Y, ¬ e.IsDiag := by
  intro e he
  obtain ⟨u, hu, v, hv, rfl⟩ := hY e he
  rw [Sym2.mk_isDiag_iff]
  intro huv
  exact Finset.disjoint_left.mp hLR hu (huv.symm ▸ hv)

theorem fresh_pair (L R : Finset V) (B Y : Finset (Sym2 V)) (M q b : ℕ)
    (hLR : Disjoint L R) (hY : Joins L R Y) (hcard : Y.card ≤ M)
    (hdeg : ∀ v, incidentLoad Y v ≤ q)
    (hB : ∀ v, incidentLoad B v ≤ b)
    (hleft : 2 * M < q * L.card)
    (hright : 2 * M + 2 * q * (b + q) < q * R.card) :
    ∃ u ∈ L, ∃ v ∈ R, s(u, v) ∉ B ∪ Y ∧
      incidentLoad Y u < q ∧ incidentLoad Y v < q := by
  let := Fintype.ofFinite V
  let Z := univ.filter (fun v => q ≤ incidentLoad Y v)
  have hsum : ∑ v, incidentLoad Y v = 2 * Y.card := by
    exact TypedCoverDown.sum_degrees_eq_two_mul_card Y (joins_loopless hLR hY)
  have hsat : q * Z.card ≤ 2 * M := by
    have h := saturated_card_budget (incidentLoad Y) q
    rw [hsum] at h
    exact h.trans (Nat.mul_le_mul_left 2 hcard)
  have hL : (L \ Z).Nonempty := by
    by_contra hn
    have hsub : L ⊆ Z := by
      intro u hu
      by_contra hz
      exact hn ⟨u, mem_sdiff.mpr ⟨hu, hz⟩⟩
    have hc := Nat.mul_le_mul_left q (card_le_card hsub)
    omega
  obtain ⟨u, hu⟩ := hL
  have huL := (mem_sdiff.mp hu).1
  have huZ := (mem_sdiff.mp hu).2
  have huq : incidentLoad Y u < q := by
    simpa only [Z, mem_filter, mem_univ, true_and, not_le] using huZ
  have hBY : incidentLoad (B ∪ Y) u ≤ b + q := by
    unfold incidentLoad
    rw [filter_union]
    exact (card_union_le _ _).trans (Nat.add_le_add (hB u) (hdeg u))
  let good := R \ (Z ∪ blockedNeighbours (B ∪ Y) u ∪ blockedNeighbours (B ∪ Y) u)
  have hgood : good.Nonempty := by
    by_contra hn
    have hz : good.card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)
    have hc := available_card_budget R Z (B ∪ Y) u u
    have hc' : R.card ≤ Z.card + 2 * (b + q) := by
      dsimp [good] at hz
      rw [hz] at hc
      omega
    have hm := Nat.mul_le_mul_left q hc'
    nlinarith
  obtain ⟨v, hv⟩ := hgood
  have hvR := (mem_sdiff.mp hv).1
  have hvbad := (mem_sdiff.mp hv).2
  have hvZ : v ∉ Z := by
    intro hz
    exact hvbad (mem_union_left _ (mem_union_left _ hz))
  have hve : s(u, v) ∉ B ∪ Y := by
    intro he
    exact hvbad (mem_union_right _ (mem_filter.mpr ⟨mem_univ v, he⟩))
  refine ⟨u, huL, v, hvR, hve, huq, ?_⟩
  simpa only [Z, mem_filter, mem_univ, true_and, not_le] using hvZ

omit [Finite V] in
theorem incident_insert (Y : Finset (Sym2 V)) (u v w : V) (q : ℕ)
    (hfresh : s(u, v) ∉ Y) (hdeg : ∀ z, incidentLoad Y z ≤ q)
    (hu : incidentLoad Y u < q) (hv : incidentLoad Y v < q) :
    incidentLoad (insert s(u, v) Y) w ≤ q := by
  unfold incidentLoad
  by_cases hw : w ∈ s(u, v)
  · have hf : s(u, v) ∉ Y.filter (fun e => w ∈ e) := by simp [hfresh]
    rw [filter_insert, ite_eq_left hw, card_insert_of_notMem hf]
    rcases Sym2.mem_iff.mp hw with rfl | rfl
    · exact Nat.succ_le_of_lt hu
    · exact Nat.succ_le_of_lt hv
  · rw [filter_insert, ite_eq_right hw]
    exact hdeg w

/-- Any prescribed number of fresh cross pairs up to the stated capacity is
realized with maximum degree at most the quota. The two parts can be arbitrary
disjoint finite sets; completeness is used when these pairs are later made
edges of the host graph. -/
theorem exists_edges_of_quota (L R : Finset V) (B : Finset (Sym2 V))
    (M q b : ℕ) (hLR : Disjoint L R)
    (hB : ∀ v, incidentLoad B v ≤ b)
    (hleft : 2 * M < q * L.card)
    (hright : 2 * M + 2 * q * (b + q) < q * R.card) :
    ∀ m ≤ M, ∃ Y : Finset (Sym2 V), Y.card = m ∧
      Joins L R Y ∧ Disjoint Y B ∧ ∀ v, incidentLoad Y v ≤ q := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨∅, card_empty, by simp [Joins], disjoint_empty_left B, by simp [incidentLoad]⟩
  | succ m ih =>
    intro hm
    obtain ⟨Y, hcard, hY, hYB, hdeg⟩ := ih (Nat.le_trans (Nat.le_succ m) hm)
    obtain ⟨u, hu, v, hv, hfresh, huq, hvq⟩ := fresh_pair L R B Y M q b hLR hY
      (by omega) hdeg hB hleft hright
    have hnY : s(u, v) ∉ Y := fun he => hfresh (mem_union_right B he)
    have hnB : s(u, v) ∉ B := fun he => hfresh (mem_union_left Y he)
    refine ⟨insert s(u, v) Y, ?_, ?_, ?_, ?_⟩
    · rw [card_insert_of_notMem hnY, hcard]
    · intro e he
      rcases mem_insert.mp he with rfl | he
      · exact ⟨u, hu, v, hv, rfl⟩
      · exact hY e he
    · exact disjoint_insert_left.mpr ⟨hnB, hYB⟩
    · exact fun w => incident_insert Y u v w q hnY hdeg huq hvq

end PartitionedTriangleAbsorption.BipartiteQuotaStage76
