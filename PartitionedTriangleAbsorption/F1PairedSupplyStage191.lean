/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1BoundaryRepairStage190

/-! # Paired-root supply and the one-request-per-root budget

Paired-root abundance follows from the real own-label neighbourhood, not from
global type counts. The boundary correction requires only a constant request
at each root and has a linear maximum-degree cost.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1PairedSupplyStage191

open Finset TypedApplicationLinks F1RootCountsStage182 TypedHostMassStage176

variable {V : Type} [Fintype V] [DecidableEq V]

theorem same_neighbours_le_degree (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (v : V) :
    ((univ.filter fun u => p u = p v ∧ G.Adj v u).card : ℤ) ≤
      degVec p G.edgeFinset v (p v) := by
  classical
  let A := univ.filter fun u => p u = p v ∧ G.Adj v u
  have hsub : A.image (fun u => s(v, u)) ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨u, hu, rfl⟩ := mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr (mem_filter.mp hu).2.2
  have hinj : Set.InjOn (fun u => s(v, u)) A := by
    intro u _ w _ h
    rcases Sym2.eq_iff.mp h with h | h
    · exact h.2
    · exact h.2.trans h.1
  have hsum : (∑ e ∈ A.image (fun u => s(v, u)), degContrib p v e (p v)) = A.card := by
    rw [sum_image hinj]
    have hval : ∀ u ∈ A, degContrib p v s(v, u) (p v) = 1 := by
      intro u hu
      obtain ⟨hlabel, hadj⟩ := (mem_filter.mp hu).2
      simp [degContrib, hadj.ne.symm, hlabel]
    simp_rw [sum_congr rfl hval]
    simp
  have h := sum_le_sum_of_subset_of_nonneg hsub
    (fun e _ _ => TypedDivisibilityCollapse.degContrib_nonneg p v e (p v))
  rw [hsum] at h
  simpa only [A, degVec, Finset.sum_apply] using h

theorem paired_supply_from_host (p : V → Fin 4) (G : SimpleGraph V)
    [DecidableRel G.Adj] (Q : Finset (Sym2 V)) (D : Finset (Finset V))
    (hD : IsDecomp p F1 Q D) (hQ : Q ⊆ G.edgeFinset)
    (v : V) (α ε ξ : ℝ)
    (hsize : α * Fintype.card V ≤ ((univ.filter fun u => p u = p v).card : ℝ))
    (hmiss : ((univ.filter fun u => p u = p v ∧ ¬ G.Adj v u).card : ℝ) ≤
      ε * Fintype.card V)
    (hres : ((G.edgeFinset \ Q).filter fun e => v ∈ e).card ≤ ξ * Fintype.card V) :
    (α - ε - ξ) * Fintype.card V ≤ ((pairedFamily p D v).card : ℝ) := by
  classical
  let C := univ.filter fun u => p u = p v
  have hm : ((C.filter fun u => ¬ G.Adj v u).card : ℝ) ≤ ε * Fintype.card V := by
    simpa [C, filter_filter] using hmiss
  have hgood := filter_card_lower C (G.Adj v) _ hm
  have hown := same_neighbours_le_degree p G v
  have hown' : ((C.filter (G.Adj v)).card : ℝ) ≤ (degVec p G.edgeFinset v (p v) : ℝ) := by
    simpa [C, filter_filter] using (show
      ((univ.filter fun u => p u = p v ∧ G.Adj v u).card : ℝ) ≤
        (degVec p G.edgeFinset v (p v) : ℝ) by exact_mod_cast hown)
  have hpart := congrFun
    (degVec_union p (disjoint_sdiff : Disjoint Q (G.edgeFinset \ Q)) v) (p v)
  rw [union_sdiff_of_subset hQ] at hpart
  simp only [Pi.add_apply] at hpart
  have hcount := (packing_root_counts p Q D hD v).2
  have hnonneg : ∀ j, 0 ≤ degVec p (G.edgeFinset \ Q) v j := by
    intro j
    simp only [degVec, Finset.sum_apply]
    exact sum_nonneg fun e _ => TypedDivisibilityCollapse.degContrib_nonneg p v e j
  have hsum := TypedDivisibilityCollapse.sum_degVec p (G.edgeFinset \ Q)
    (fun e he => G.not_isDiag_of_mem_edgeSet (SimpleGraph.mem_edgeFinset.mp (mem_sdiff.mp he).1)) v
  have hbound := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) => hnonneg j)
    (mem_univ (p v))
  rw [hsum] at hbound
  have hbound' : (degVec p (G.edgeFinset \ Q) v (p v) : ℝ) ≤
      ((G.edgeFinset \ Q).filter fun e => v ∈ e).card := by exact_mod_cast hbound
  have hp : (degVec p G.edgeFinset v (p v) : ℝ) =
      (pairedFamily p D v).card + (degVec p (G.edgeFinset \ Q) v (p v) : ℝ) := by
    rw [hcount] at hpart
    exact_mod_cast hpart
  dsimp [C] at hgood
  linarith

theorem boundary_budget (n S : ℕ) (κ : ℝ) (hκ : 0 < κ)
    (hscale : 16 ≤ κ * n) (hsquare : 192 ≤ κ ^ 2 * n)
    (hS : κ * n ≤ (S : ℝ)) :
    let d := ⌊κ * n / 8⌋₊
    0 < d ∧ d * (d + 1) + 3 * n < d * S ∧
      (2 * (d + 1) : ℕ) ≤ κ * n / 2 := by
  dsimp
  have hn : (0 : ℝ) < n := by nlinarith
  have hdhi : (⌊κ * n / 8⌋₊ : ℝ) ≤ κ * n / 8 := Nat.floor_le (by positivity)
  have hdlo : κ * n / 16 ≤ (⌊κ * n / 8⌋₊ : ℝ) := by
    have h := Nat.lt_floor_add_one (κ * (n : ℝ) / 8)
    linarith
  have hdk : (⌊κ * n / 8⌋₊ : ℝ) + 1 ≤ κ * n / 4 := by linarith
  have hp := mul_le_mul hdhi hdk (by positivity) (by positivity)
  have hr := mul_le_mul hdlo hS (by positivity) (by positivity)
  have hs := mul_le_mul_of_nonneg_right hsquare hn.le
  refine ⟨Nat.floor_pos.mpr (by linarith), ?_, ?_⟩
  · have h : (⌊κ * n / 8⌋₊ : ℝ) * ((⌊κ * n / 8⌋₊ : ℝ) + 1) +
        3 * n < (⌊κ * n / 8⌋₊ : ℝ) * S := by nlinarith
    exact_mod_cast h
  · push_cast
    linarith

end PartitionedTriangleAbsorption.F1PairedSupplyStage191

