/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BipartiteQuotaStage76

/-! # Bounded-degree selection inside a supplied physical edge pool

Unlike the complete bipartite selector, this selector never invents a pair:
every chosen edge belongs to the given loopless pool. It will be used to trim
surplus type counts of a vortex reserve without concentrated degree losses.
The pool-size inequality is explicit; no selector is supplied as a premise.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PoolQuotaStage109

open Finset AntiEdgeSelection

variable {V : Type*} [Finite V] [DecidableEq V]

theorem fresh_edge (R Y : Finset (Sym2 V)) (M q D : ℕ)
    (hR : ∀ e ∈ R, ¬ e.IsDiag) (hYR : Y ⊆ R) (hYcard : Y.card ≤ M)
    (hRdeg : ∀ v, incidentLoad R v ≤ D)
    (hbudget : 2 * M * D + M * q < q * R.card) :
    ∃ e ∈ R, e ∉ Y ∧ ∀ v ∈ e, incidentLoad Y v < q := by
  let := Fintype.ofFinite V
  let Z := univ.filter (fun v => q ≤ incidentLoad Y v)
  have hsum : ∑ v, incidentLoad Y v = 2 * Y.card :=
    TypedCoverDown.sum_degrees_eq_two_mul_card Y (fun e he => hR e (hYR he))
  have hsat : q * Z.card ≤ 2 * M := by
    have h := saturated_card_budget (incidentLoad Y) q
    rw [hsum] at h
    exact h.trans (Nat.mul_le_mul_left 2 hYcard)
  let Bad := Z.biUnion (fun v => R.filter (fun e => v ∈ e))
  have hbad : Bad.card ≤ Z.card * D := by
    calc Bad.card ≤ ∑ v ∈ Z, (R.filter (fun e => v ∈ e)).card := card_biUnion_le
      _ ≤ ∑ _v ∈ Z, D := sum_le_sum (fun v _ => hRdeg v)
      _ = Z.card * D := by simp
  by_contra hno
  push Not at hno
  have hsub : R ⊆ Y ∪ Bad := by
    intro e he
    by_cases heY : e ∈ Y
    · exact mem_union_left _ heY
    obtain ⟨v, hv, hload⟩ := hno e he heY
    exact mem_union_right _ (mem_biUnion.mpr
      ⟨v, mem_filter.mpr ⟨mem_univ v, hload⟩, mem_filter.mpr ⟨he, hv⟩⟩)
  have hcard := (card_le_card hsub).trans (card_union_le Y Bad)
  have hmul := Nat.mul_le_mul_left q hcard
  have hsatD := Nat.mul_le_mul_right D hsat
  nlinarith

/-- A bounded-degree subpool of any requested size up to `M`, under the same
capacity bound. The conclusion keeps literal physical containment. -/
theorem exists_subpool (R : Finset (Sym2 V)) (M q D : ℕ)
    (hR : ∀ e ∈ R, ¬ e.IsDiag) (hRdeg : ∀ v, incidentLoad R v ≤ D)
    (hbudget : 2 * M * D + M * q < q * R.card) :
    ∀ m ≤ M, ∃ Y ⊆ R, Y.card = m ∧ ∀ v, incidentLoad Y v ≤ q := by
  intro m
  induction m with
  | zero =>
    intro _
    exact ⟨∅, empty_subset _, card_empty, by simp [incidentLoad]⟩
  | succ m ih =>
    intro hm
    obtain ⟨Y, hYR, hc, hd⟩ := ih (by omega)
    obtain ⟨e, heR, heY, heq⟩ := fresh_edge R Y M q D hR hYR (by omega) hRdeg hbudget
    refine ⟨insert e Y, insert_subset heR hYR, ?_, ?_⟩
    · rw [card_insert_of_notMem heY, hc]
    · induction e using Sym2.ind with
      | _ u v =>
        exact fun w => BipartiteQuotaStage76.incident_insert Y u v w q heY hd
          (heq u (Sym2.mem_mk_left u v)) (heq v (Sym2.mem_mk_right u v))

end PartitionedTriangleAbsorption.PoolQuotaStage109
