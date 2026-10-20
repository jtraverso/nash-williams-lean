/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.IndependentStarQuotaStage144
public import PartitionedTriangleAbsorption.ExceptionalGeometryStage141

/-! # Star inventories from actual neighbours in four colour classes

Only the local half-degree bounds remain explicit. The global three column
bounds and total budget are consequences of the graph, not input assumptions.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.GraphStarInventoryStage144

open Finset MatchedQuotaStage140 IndependentStarQuotaStage144

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def classLoad (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (j : Fin 4) : ℕ :=
  (G.neighborFinset v |>.filter fun w => p w = j).card

theorem label_inventory (j k : Fin 4) :
    (if k = j then 1 else 0) +
      (∑ i : Fin 3, if k = partner i j then (1 : ℕ) else 0) = 1 := by
  fin_cases j <;> fin_cases k <;> decide

theorem same_labels (i : Fin 3) (j k : Fin 4) :
    side i k = side i j ↔ k = j ∨ k = partner i j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

omit [DecidableEq V] in
theorem degree_inventory (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    classLoad p G v (p v) + (∑ i : Fin 3, classLoad p G v (partner i (p v))) =
      G.degree v := by
  classical
  have hc (j : Fin 4) : classLoad p G v j =
      ∑ w ∈ G.neighborFinset v, if p w = j then 1 else 0 := by
    rw [← sum_filter]
    simp [classLoad]
  simp_rw [hc]
  rw [sum_comm, ← sum_add_distrib]
  simp_rw [label_inventory]
  simp

theorem same_load_neighbor {K : Type*} [DecidableEq K] (p : V → K)
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    sameLoad p G.edgeFinset v = (G.neighborFinset v |>.filter fun w => p w = p v).card := by
  classical
  symm
  apply card_bij (fun w _ => s(v, w))
  · intro w hw
    obtain ⟨hwG, hw⟩ := mem_filter.mp hw
    refine mem_filter.mpr ⟨by simpa using hwG, ?_⟩
    exact ⟨by simp, by simpa [Sym2.map_mk, Sym2.mk_isDiag_iff] using hw.symm⟩
  · intro a _ c _ he
    rcases Sym2.eq_iff.mp he with he | he
    · exact he.2
    · exact he.2.trans he.1
  · intro e he
    obtain ⟨heG, hve, hp⟩ := mem_filter.mp he
    induction e using Sym2.ind with
    | _ a c =>
      simp only [Sym2.mem_iff] at hve
      simp only [Sym2.map_mk, Sym2.mk_isDiag_iff] at hp
      rcases hve with rfl | rfl
      · exact ⟨c, mem_filter.mpr ⟨by simpa using heG, hp.symm⟩, rfl⟩
      · refine ⟨a, mem_filter.mpr ⟨?_, hp⟩, Sym2.eq_swap⟩
        have hG : G.Adj a v := by simpa using heG
        exact (G.mem_neighborFinset v a).mpr hG.symm

theorem internal_inventory (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    classLoad p G v (p v) = AntiEdgeSelection.incidentLoad (internal p G.edgeFinset) v := by
  classical
  have he : (internal p G.edgeFinset).filter (fun e : Sym2 V => v ∈ e) =
      G.edgeFinset.filter (fun e : Sym2 V => v ∈ e ∧ (e.map p).IsDiag) := by
    ext e
    simp only [internal, mem_filter]
    tauto
  rw [AntiEdgeSelection.incidentLoad, he]
  exact (same_load_neighbor p G v).symm

theorem same_inventory (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (i : Fin 3) :
    classLoad p G v (p v) + classLoad p G v (partner i (p v)) =
      sameLoad (side i ∘ p) G.edgeFinset v := by
  classical
  rw [same_load_neighbor]
  have hc (j : Fin 4) : classLoad p G v j =
      ∑ w ∈ G.neighborFinset v, if p w = j then 1 else 0 := by
    rw [← sum_filter]
    simp [classLoad]
  rw [hc, hc, ← sum_add_distrib]
  have hs : (G.neighborFinset v |>.filter fun w => (side i ∘ p) w = (side i ∘ p) v).card =
      ∑ w ∈ G.neighborFinset v, if (side i ∘ p) w = (side i ∘ p) v then 1 else 0 := by
    rw [← sum_filter]
    simp
  rw [hs]
  apply sum_congr rfl
  intro w _
  simp only [Function.comp_apply, same_labels]
  have hn := partner_ne i (p v)
  by_cases h0 : p w = p v <;> by_cases h1 : p w = partner i (p v) <;> simp_all

omit [DecidableEq V] in
theorem exists_inventory_allocation (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) (h : V → ℕ) (q : Fin 3 → ℕ)
    (hdegree : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v)
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hhalf : ∀ v ∈ S, G.degree v = 2 * h v)
    (hlocal : ∀ v ∈ S, ∀ j, classLoad p G v j ≤ h v)
    (hq : ∀ i, 6 * q i + 3 * (cuts p G.edgeFinset i).card = 2 * G.edgeFinset.card)
    (hqsum : (∑ i, q i) = (internal p G.edgeFinset).card) :
    ∃ x : S → Fin 3 → ℕ,
      (∀ v : S, ∑ i, x v i = classLoad p G v (p v)) ∧
      (∀ (v : S) i,
        classLoad p G v (p v) + classLoad p G v (partner i (p v)) - h v ≤ x v i ∧
          x v i ≤ classLoad p G v (partner i (p v))) ∧
      (∀ i, ∑ v, x v i ≤ q i) := by
  classical
  apply exists_graph_star_counts p G S h (fun v => classLoad p G v (p v))
    (fun v i => classLoad p G v (partner i (p v))) q hdegree hS hhalf
    (fun v _ => internal_inventory p G v) (fun v _ i => same_inventory p G v i)
    (fun v hv => (degree_inventory p G v).trans (hhalf v hv))
    (fun v hv => ⟨hlocal v hv (p v), fun i => hlocal v hv (partner i (p v))⟩)
    hq hqsum

omit [DecidableEq V] in
theorem classLoad_le_class_card (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) (j : Fin 4) :
    classLoad p G v j ≤ (univ.filter fun w => p w = j).card := by
  classical
  apply card_le_card
  intro w hw
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hw).2⟩

/-- A graph-only allocation theorem. No forced column bounds, cut tests,
real flow, or supplied quotas occur among its hypotheses. -/
theorem exists_allocation_of_graph (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V)
    (hdegree : ∀ v, 3 * Fintype.card V ≤ 4 * G.degree v)
    (hdiv : OnePart.Even3 G.edgeFinset)
    (hS : ∀ u ∈ S, ∀ v ∈ S, ¬ G.Adj u v)
    (hclasses : ∀ j, 8 * (univ.filter fun w => p w = j).card ≤ 3 * Fintype.card V) :
    ∃ q : Fin 3 → ℕ, ∃ x : S → Fin 3 → ℕ,
      (∀ i, 6 * q i + 3 * (cuts p G.edgeFinset i).card = 2 * G.edgeFinset.card) ∧
      (∑ i, q i) = (internal p G.edgeFinset).card ∧
      (∀ v : S, ∑ i, x v i = classLoad p G v (p v)) ∧
      (∀ (v : S) i,
        classLoad p G v (p v) + classLoad p G v (partner i (p v)) - G.degree v / 2 ≤ x v i ∧
          x v i ≤ classLoad p G v (partner i (p v))) ∧
      (∀ i, ∑ v, x v i ≤ q i) := by
  classical
  obtain ⟨q, hq, hqsum⟩ := exists_quotas p G.edgeFinset
    (fun e he => G.not_isDiag_of_mem_edgeFinset he) hdiv
    (CutSurplusStage140.surplus_of_degree p G hdegree)
  have hh (v : V) : G.degree v = 2 * (G.degree v / 2) := by
    obtain ⟨d, hd⟩ := hdiv.2 v
    rw [incident_degree G v] at hd
    omega
  have hl (v : V) (j : Fin 4) : classLoad p G v j ≤ G.degree v / 2 := by
    have hc := hclasses j
    have hd := hdegree v
    have he := hh v
    have hb := classLoad_le_class_card p G v j
    omega
  obtain ⟨x, hxrow, hxcap, hxcol⟩ := exists_inventory_allocation p G S
    (fun v => G.degree v / 2) q hdegree hS (fun v _ => hh v)
    (fun v _ j => hl v j) hq hqsum
  exact ⟨q, x, hq, hqsum, hxrow, hxcap, hxcol⟩

omit [DecidableEq V] in
theorem class_budget_of_average (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (rho : ℝ) (hrho : 0 ≤ rho) (hsmall : rho ≤ 1 / 64)
    (hn : 0 < Fintype.card V)
    (hdegree : ∀ v, (3 / 4 : ℝ) * Fintype.card V ≤ G.degree v)
    (herr : ((internal p G.edgeFinset).card : ℝ) ≤ rho * (Fintype.card V : ℝ) ^ 2)
    (j : Fin 4) :
    8 * (univ.filter fun w => p w = j).card ≤ 3 * Fintype.card V := by
  have hc := ExceptionalGeometryStage141.class_upper_average G p rho hrho hn hdegree herr j
  have hn0 : (0 : ℝ) ≤ Fintype.card V := Nat.cast_nonneg _
  have hs := mul_le_mul_of_nonneg_right hsmall hn0
  have hb : (8 : ℝ) * (univ.filter fun w => p w = j).card ≤ 3 * Fintype.card V := by
    change ((univ.filter fun w => p w = j).card : ℝ) ≤
      (1 / 4 + 8 * rho) * Fintype.card V at hc
    nlinarith
  exact_mod_cast hb

end PartitionedTriangleAbsorption.GraphStarInventoryStage144
