/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.TypedDegreeReserveStage115
public import PartitionedTriangleAbsorption.SeedDrivenTrimStage114
public import PartitionedTriangleAbsorption.DegreeReserveBudgetStage115

/-! # Producing the reserve and its balanced trimming together

The complement of the sampled reserve is protected. No small-degree bound
on that complement is imposed. The result cancels the linear F3 charges;
it does not claim that the removed edges are independently decomposable.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SampledReserveTrimStage115

open Finset AntiEdgeSelection TypedNibble TypedApplicationLinks TypedLoadNecessity
  CoverDownStage105 F3ReserveTrimStage109 ReserveTrimStage109 SeedDrivenTrimStage114
  TypedDegreeReserveStage115

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem category_zero_succ (i : Fin 3) : categoryTab 0 i.succ = i := by
  revert i
  decide

theorem exists_trim_of_typed_degrees
    (p : V → Fin 4) (J : SimpleGraph V) [DecidableRel J.Adj]
    (φ : Finset V → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε)
    (hcross : ∀ u v, J.Adj u v → p u ≠ p v)
    (m D a b : ℕ) (hm : 2 * ε * J.edgeFinset.card ≤ (m : ℝ)) (hcap : m < a * b)
    (hclass : a ≤ (univ.filter (fun u => p u = 0)).card)
    (R : Finset (Sym2 V)) (hR : R ⊆ J.edgeFinset)
    (hdeg : ∀ v, incidentLoad R v ≤ D)
    (hrich : ∀ u i, i ≠ p u → b ≤
      (neighbours p (ReserveCoverDown.reserveGraph R) u i).card) :
    ∃ Y ⊆ R, (∀ v, incidentLoad Y v ≤ 3 * quota m D (a * b)) ∧
      ∀ k : Fin 2, bal p k (J.edgeFinset \ Y) = 0 := by
  classical
  let X := J.edgeFinset \ R
  have hhost : X ∪ R = J.edgeFinset := sdiff_union_of_subset hR
  have hdiff : R \ X = R := by ext e; simp only [X, mem_sdiff]; tauto
  let A := univ.filter (fun u => p u = 0)
  let B := fun i : Fin 3 => fun u => neighbours p (ReserveCoverDown.reserveGraph R) u i.succ
  have hB : ∀ i u, u ∈ A → b ≤ (B i u).card := by
    intro i u hu
    apply hrich
    rw [(mem_filter.mp hu).2]
    exact Fin.succ_ne_zero i
  have hout : ∀ i u, u ∈ A → ∀ v ∈ B i u, v ∉ A := by
    intro i u _ v hv ha
    have hvlabel := (mem_filter.mp hv).2.1
    have halabel := (mem_filter.mp ha).2
    exact Fin.succ_ne_zero i (hvlabel.symm.trans halabel)
  have hedge : ∀ i u, u ∈ A → ∀ v ∈ B i u,
      s(u, v) ∈ pool (category p) (R \ X) i := by
    intro i u hu v hv
    have huv := (mem_filter.mp hv).2
    rw [hdiff]
    apply mem_filter.mpr
    refine ⟨(SimpleGraph.fromEdgeSet_adj _).mp huv.2 |>.1, ?_⟩
    change categoryTab (p u) (p v) = i
    rw [(mem_filter.mp hu).2, huv.1, category_zero_succ]
  obtain ⟨Y, hY, hd, hb⟩ := exists_trim_of_seed_and_neighbours p J X R hhost
    φ ε hε hload hcross m D (a * b) hm hcap hdeg (fun _ => A) B (fun _ => b)
    hB hout hedge (fun _ => Nat.mul_le_mul_right b hclass)
  exact ⟨Y, hdiff ▸ hY, hd, hb⟩

/-- One-level reserve and recut, starting from typed host degrees and seed
loads. All reserve edges are selected inside the actual host. -/
theorem exists_sampled_trim
    (p : V → Fin 4) (J : SimpleGraph V) [DecidableRel J.Adj]
    (φ : Finset V → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε)
    (hcross : ∀ u v, J.Adj u v → p u ≠ p v)
    (β ρ : ℝ) (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hn : 0 < (Fintype.card V : ℝ))
    (hG : ∀ u i, i ≠ p u → β * Fintype.card V ≤ (neighbours p J u i).card)
    (hsize : 64 ≤ β ^ 2 * ρ ^ 4 * Fintype.card V)
    (hdegrees : 2 ≤ ρ ^ 4 * Fintype.card V)
    (m D a b : ℕ) (hm : 2 * ε * J.edgeFinset.card ≤ (m : ℝ)) (hcap : m < a * b)
    (hD : 2 * ρ * Fintype.card V ≤ (D : ℝ))
    (hb : (b : ℝ) ≤ β * ρ / 2 * Fintype.card V)
    (hclass : a ≤ (univ.filter (fun u => p u = 0)).card) :
    ∃ R ⊆ J.edgeFinset, (∀ v, incidentLoad R v ≤ D) ∧
      (∀ u i, i ≠ p u → b ≤
        (neighbours p (ReserveCoverDown.reserveGraph R) u i).card) ∧
      ∃ Y ⊆ R, (∀ v, incidentLoad Y v ≤ 3 * quota m D (a * b)) ∧
        ∀ k : Fin 2, bal p k (J.edgeFinset \ Y) = 0 := by
  have hbudget := (DegreeReserveBudgetStage115.failure_budget
    (Fintype.card V) β ρ hn.le hβ.le hsize hdegrees).trans_lt (by norm_num : (3 : ℝ) / 4 < 1)
  obtain ⟨R, hR, hd, hr⟩ := exists_reserve p J β ρ hβ hρ hρ1 hn hG hbudget
  have hd' : ∀ v, incidentLoad R v ≤ D := by
    intro v
    have h : (incidentLoad R v : ℝ) ≤ (D : ℝ) := (hd v).trans hD
    exact_mod_cast h
  have hr' : ∀ u i, i ≠ p u → b ≤
      (neighbours p (ReserveCoverDown.reserveGraph R) u i).card := by
    intro u i hi
    exact_mod_cast hb.trans (hr u i hi)
  exact ⟨R, hR, hd', hr', exists_trim_of_typed_degrees p J φ ε hε hload hcross
    m D a b hm hcap hclass R hR hd' hr'⟩

end PartitionedTriangleAbsorption.SampledReserveTrimStage115
