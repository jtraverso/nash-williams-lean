/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.WeightedRoutingBudget

/-! One physical vertex-selection step of the weighted routing induction.
Heavy vertices are measured by the whole-library auxiliary load. -/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

open Finset PartitionedTriangleAbsorption AntiEdgeSelection StructuralF3General

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

theorem heavy_load_card (load : V → ℝ) (threshold : ℝ)
    (hload : ∀ v, 0 ≤ load v) :
    ((univ.filter fun v => threshold ≤ load v).card : ℝ) * threshold ≤
      ∑ v, load v := by
  classical
  calc
    _ = ∑ v ∈ univ.filter (fun v => threshold ≤ load v), threshold := by simp
    _ ≤ ∑ v ∈ univ.filter (fun v => threshold ≤ load v), load v :=
      sum_le_sum fun v hv => (mem_filter.mp hv).2
    _ ≤ ∑ v, load v := sum_le_sum_of_subset_of_nonneg
      (filter_subset _ _) (fun v _ _ => hload v)

theorem weighted_heavy_card (load : V → ℝ) (K L lam rho n : ℝ)
    (hload : ∀ v, 0 ≤ load v) (hK : 0 < K) (hlam : 0 < lam) (hn : 0 < n)
    (htotal : ∑ v, load v ≤ 84 * L * K * rho * n ^ 2) :
    ((univ.filter fun v => 4 * K * lam * n ≤ load v).card : ℝ) ≤
      (21 * L * rho / lam) * n := by
  classical
  apply (mul_le_mul_iff_left₀ (show 0 < 4 * K * lam * n by positivity)).mp
  calc
    _ ≤ ∑ v, load v := heavy_load_card load _ hload
    _ ≤ 84 * L * K * rho * n ^ 2 := htotal
    _ = _ := by field_simp; ring

/-- A step with at most two adjacency constraints admits an unsaturated
auxiliary, outside the partial path and avoiding every previously used edge. -/
theorem weighted_routing_vertex (p : V → Fin t) (G : SimpleGraph V)
    [DecidableRel G.Adj] (Allowed : Fin t → Fin t → Prop)
    (K L lam rho omega : ℝ) (hK : 1 ≤ K) (hL : 0 ≤ L)
    (hlam : 0 < lam) (hrho : 0 ≤ rho) (hn : 0 < Fintype.card V)
    (hsmall : 64 * K * lam ≤ omega) (hratio : 128 * L * rho ≤ omega * lam)
    (hrholam : rho ≤ lam) (horder : 4 * (L + 1) ≤ omega * Fintype.card V)
    (hs : GuardedSupply p G Allowed 2 (omega * Fintype.card V))
    (load : V → ℝ) (hload : ∀ v, 0 ≤ load v)
    (htotal : ∑ v, load v ≤ 84 * L * K * rho * (Fintype.card V : ℝ) ^ 2)
    (B : Finset (Sym2 V))
    (hB : DegBounded B ((7 * K * lam + 2 * rho) * Fintype.card V))
    (S Z : Finset V) (hS : S.card ≤ 2) (hZ : (Z.card : ℝ) ≤ L + 1)
    (i : Fin t) (hguard : ∀ u ∈ S, Allowed (p u) i) :
    ∃ w, p w = i ∧ (∀ u ∈ S, G.Adj u w) ∧ w ∉ Z ∧
      load w < 4 * K * lam * Fintype.card V ∧ ∀ u ∈ S, s(u,w) ∉ B := by
  classical
  let H := univ.filter fun v => 4 * K * lam * Fintype.card V ≤ load v
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  have hH := weighted_heavy_card load K L lam rho (Fintype.card V)
    hload (by linarith) hlam hnR htotal
  have hcard : ((H ∪ Z).card : ℝ) ≤ (21 * L * rho / lam) * Fintype.card V + (L + 1) := by
    have hu : ((H ∪ Z).card : ℝ) ≤ (H.card : ℝ) + Z.card := by
      exact_mod_cast card_union_le H Z
    change (H.card : ℝ) ≤ _ at hH
    linarith
  have hbudget := weighted_routing_choice_budget K L lam rho omega (Fintype.card V)
    hK hL hlam hrho hnR hsmall hratio hrholam horder
  obtain ⟨w, hw, hadj, hout, hedges⟩ := guarded_exists_avoiding p G Allowed 2
    (omega * Fintype.card V) ((7 * K * lam + 2 * rho) * Fintype.card V)
    hs S (H ∪ Z) hS B hB (by positivity) (by norm_num; linarith) i hguard
  have hwH : w ∉ H := fun h => hout (mem_union_left _ h)
  refine ⟨w, hw, hadj, (fun h => hout (mem_union_right _ h)), ?_, hedges⟩
  have : ¬ 4 * K * lam * Fintype.card V ≤ load w := by
    intro h
    exact hwH (mem_filter.mpr ⟨mem_univ _, h⟩)
  exact lt_of_not_ge this

#print axioms heavy_load_card
#print axioms weighted_heavy_card
#print axioms weighted_routing_vertex

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
