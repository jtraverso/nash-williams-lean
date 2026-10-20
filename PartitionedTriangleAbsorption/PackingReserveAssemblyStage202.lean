/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReservePhysicalDegreeStage201
public import PartitionedTriangleAbsorption.SparseReserveAssembly

/-! # One simultaneous reserve selected from physical packing triangles

The graph-computable input is anti-edgefulness of the packing union.
The good outcome is constructed from an explicit failure budget.
Absorption of a later residual inside the reserve is not asserted.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.PackingReserveAssemblyStage202

open Finset MeasureTheory ProbabilityTheory BernoulliBlocks ReservePhysicalQueryStage200

variable {V : Type} [Fintype V] [DecidableEq V] {t : ℕ}

noncomputable def candidates (Q : Finset (Sym2 V)) (p : V → Fin t) (u v : V) (k : Fin t) :
    Finset V := by
  classical
  exact univ.filter fun w => u ≠ w ∧ v ≠ w ∧ s(u, w) ∈ Q ∧ s(v, w) ∈ Q ∧ p w = k

theorem candidate_count_eq (Q : Finset (Sym2 V)) (D : Finset (Finset V))
    (hQ : D.biUnion triEdges = Q) (p : V → Fin t) (u v : V) (k : Fin t)
    (ω : Finset V → Bool) :
    neighbours D u v (candidates Q p u v k) ω =
      (univ.filter fun w => (ReserveCoverDown.reserveGraph (reserve D ω)).Adj u w ∧
        (ReserveCoverDown.reserveGraph (reserve D ω)).Adj w v ∧ p w = k) := by
  classical
  have hsub : reserve D ω ⊆ Q := by
    rw [← hQ]
    exact biUnion_subset_biUnion_of_subset_left triEdges (filter_subset _ _)
  ext w
  simp only [neighbours, candidates, mem_filter, mem_univ, true_and]
  rw [SimpleGraph.fromEdgeSet_adj, SimpleGraph.fromEdgeSet_adj]
  simp only [mem_coe, Sym2.eq_swap (a := w) (b := v)]
  constructor
  · rintro ⟨⟨huw, hvw, _, _, hp⟩, h₁, h₂⟩
    exact ⟨⟨h₁, huw⟩, ⟨h₂, hvw.symm⟩, hp⟩
  · rintro ⟨⟨h₁, huw⟩, ⟨h₂, hwv⟩, hp⟩
    exact ⟨⟨huw, hwv.symm, hsub h₁, hsub h₂, hp⟩, h₁, h₂⟩

theorem query_lower_tail (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    [DecidableRel (ReserveCoverDown.reserveGraph Q).Adj]
    (γ ρ : ℝ) (hρ : 0 < ρ) (hscale : 2 ≤ γ * Fintype.card V)
    (hG : AntiEdgeful p F (ReserveCoverDown.reserveGraph Q) γ)
    (μ : Measure (Finset V → Bool)) [IsProbabilityMeasure μ]
    (hind : iIndepSet (fun s => {ω | ω s = true}) μ)
    (hmarg : ∀ s, μ {ω | ω s = true} = ENNReal.ofReal ρ)
    (q : SparseReserveAssembly.Query p F) :
    μ.real {ω | ((neighbours D q.val.1 q.val.2.1
      (candidates Q p q.val.1 q.val.2.1 q.val.2.2) ω).card : ℝ) ≤
        γ * ρ ^ 2 / 12 * Fintype.card V} ≤
      Real.exp (-ρ ^ 4 * γ * Fintype.card V / 12) := by
  classical
  let C := candidates Q p q.val.1 q.val.2.1 q.val.2.2
  have hc : γ * Fintype.card V ≤ (C.card : ℝ) := by
    have h := hG _ q.property.2 _ _ _ rfl _ _ q.property.1 rfl rfl
    simpa only [C, candidates, ReserveCoverDown.reserveGraph, SimpleGraph.fromEdgeSet_adj,
      mem_coe, Sym2.eq_swap (a := q.val.2.1), ne_comm, and_assoc, and_left_comm, and_comm] using h
  have hC : 2 ≤ C.card := by exact_mod_cast (hscale.trans hc)
  have hlegs : ∀ w ∈ C, s(q.val.1, w) ∈ Q ∧ s(q.val.2.1, w) ∈ Q := by
    intro w hw
    have h := (mem_filter.mp hw).2
    exact ⟨h.2.2.1, h.2.2.2.1⟩
  have hroot : ∀ w ∈ C, w ≠ q.val.1 ∧ w ≠ q.val.2.1 := by
    intro w hw
    have h := (mem_filter.mp hw).2
    exact ⟨h.1.symm, h.2.1.symm⟩
  have hb := physical_query_lower_tail p F Q D hD q.val.1 q.val.2.1 q.property.1 C hC
    hlegs hroot μ hind ρ hρ.le hmarg
  have hhalf : γ * Fintype.card V / 2 ≤ (C.card : ℝ) - 1 := by linarith
  have hsub : {ω | ((neighbours D q.val.1 q.val.2.1 C ω).card : ℝ) ≤
      γ * ρ ^ 2 / 12 * Fintype.card V} ⊆
      {ω | ((neighbours D q.val.1 q.val.2.1 C ω).card : ℝ) ≤ ρ ^ 2 * (C.card - 1 : ℝ) / 6} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    nlinarith [mul_le_mul_of_nonneg_left hhalf (sq_nonneg ρ)]
  apply (measureReal_mono hsub).trans (hb.trans (Real.exp_le_exp.mpr ?_))
  nlinarith [mul_le_mul_of_nonneg_left hhalf (pow_nonneg hρ.le 4)]

theorem exists_reserve_of_budget (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (Q : Finset (Sym2 V)) (D : Finset (Finset V)) (hD : IsDecomp p F Q D)
    [DecidableRel (ReserveCoverDown.reserveGraph Q).Adj]
    (γ ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hscale : 2 ≤ γ * Fintype.card V)
    (hG : AntiEdgeful p F (ReserveCoverDown.reserveGraph Q) γ)
    (hbudget : (Fintype.card V : ℝ) * Real.exp (-ρ ^ 2 * Fintype.card V) +
      (Fintype.card V : ℝ) ^ 2 * t * Real.exp (-ρ ^ 4 * γ * Fintype.card V / 12) < 1) :
    ∃ B : Finset (Finset V), B ⊆ D ∧
      DegBounded (B.biUnion triEdges) (2 * ρ * Fintype.card V) ∧
      (let X := B.biUnion triEdges
       AntiEdgeful p F (ReserveCoverDown.reserveGraph X) (γ * ρ ^ 2 / 12)) ∧
      HasDecomp p F (B.biUnion triEdges) ∧
      (∀ v, ReserveConfinementStage195.outsideCharge D (B.biUnion triEdges) v = 0) := by
  classical
  obtain ⟨μ, hμ, hind, hmarg⟩ := exists_edge_trials (E := Finset V) ρ hρ.le hρ1
  let : IsProbabilityMeasure μ := hμ
  let bad : V ⊕ SparseReserveAssembly.Query p F → Set (Finset V → Bool)
    | Sum.inl v => {ω | 2 * ρ * Fintype.card V ≤ ((reserve D ω).filter fun e => v ∈ e).card}
    | Sum.inr q => {ω | ((neighbours D q.val.1 q.val.2.1
        (candidates Q p q.val.1 q.val.2.1 q.val.2.2) ω).card : ℝ) ≤
          γ * ρ ^ 2 / 12 * Fintype.card V}
  let bound : V ⊕ SparseReserveAssembly.Query p F → ℝ
    | Sum.inl _ => Real.exp (-ρ ^ 2 * Fintype.card V)
    | Sum.inr _ => Real.exp (-ρ ^ 4 * γ * Fintype.card V / 12)
  have htail : ∀ i, μ.real (bad i) ≤ bound i := by
    intro i
    cases i with
    | inl v =>
      exact ReservePhysicalDegreeStage201.physical_degree_upper_tail
        p F Q D hD v μ hind ρ hρ hmarg
    | inr q => exact query_lower_tail p F Q D hD γ ρ hρ hscale hG μ hind hmarg q
  have hcount : (Fintype.card (SparseReserveAssembly.Query p F) : ℝ) ≤
      (Fintype.card V : ℝ) ^ 2 * t := by exact_mod_cast SparseReserveAssembly.query_card_le p F
  have hsum : ∑ i, bound i < 1 := by
    rw [Fintype.sum_sum_type]
    simp only [bound, sum_const, card_univ, nsmul_eq_mul]
    exact (add_le_add (le_refl _)
      (mul_le_mul_of_nonneg_right hcount (Real.exp_pos _).le)).trans_lt hbudget
  obtain ⟨ω, hω⟩ := PhysicalReserveTails.exists_simultaneous_outcome μ bad bound htail hsum
  let B := selected D ω
  have hBD : B ⊆ D := filter_subset _ _
  refine ⟨B, hBD, ?_, ?_, ⟨B, fun s hs => hD.1 s (hBD hs), hD.2.1.subset hBD, rfl⟩,
    fun v => ReserveConfinementStage195.outside_charge_zero_of_whole_triangles p F Q D B hD hBD v⟩
  · intro v
    exact (not_le.mp (hω (Sum.inl v))).le
  · dsimp (config := { failIfUnchanged := false }) only
    intro τ hτ i j k hτeq u v huv hu hv
    let q : SparseReserveAssembly.Query p F :=
      ⟨(u, v, k), huv, by simpa only [hu, hv, hτeq] using hτ⟩
    have hnq : ¬ ((neighbours D u v (candidates Q p u v k) ω).card : ℝ) ≤
        γ * ρ ^ 2 / 12 * Fintype.card V := hω (Sum.inr q)
    have h : γ * ρ ^ 2 / 12 * Fintype.card V ≤
        ((neighbours D u v (candidates Q p u v k) ω).card : ℝ) := (not_le.mp hnq).le
    rw [candidate_count_eq Q D hD.2.2 p u v k ω] at h
    exact h


end PartitionedTriangleAbsorption.PackingReserveAssemblyStage202
