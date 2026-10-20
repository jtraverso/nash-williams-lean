/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ReserveAwareRecutStage120

/-! # Charge a protected reserve to the recut budget

The category discrepancy of the union is derived, not supplied separately.
The cardinality charge is conservative; the capacity inequality remains an
explicit check. Neighbour witnesses are counted in the actual child pool.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.ReserveChargeStage121

open Finset TypedApplicationLinks TypedLoadNecessity ApproximateBalanceStage114
  ReserveTrimStage109 F3ReserveTrimStage109 AntiEdgeSelection CoverDownStage105
  SeedDrivenTrimStage114 NeighbourPoolCapacityStage114 ReserveAwareRecutStage120

variable {V : Type*} [DecidableEq V]

theorem union_discrepancy (c : Sym2 V → Fin 3) (R J : Finset (Sym2 V)) (m : ℕ)
    (hJ : ∀ i j, (pool c J i).card ≤ (pool c J j).card + m) :
    ∀ i j, (pool c (R ∪ J) i).card ≤ (pool c (R ∪ J) j).card + (m + R.card) := by
  intro i j
  have hu : pool c (R ∪ J) i = pool c R i ∪ pool c J i := by
    simp only [pool, filter_union]
  have hRi : (pool c R i).card ≤ R.card := card_filter_le _ _
  have hJj : (pool c J j).card ≤ (pool c (R ∪ J) j).card :=
    card_le_card (filter_subset_filter _ subset_union_right)
  have hc := card_union_le (pool c R i) (pool c J i)
  rw [← hu] at hc
  have hh := hJ i j
  omega

variable [Fintype V]

theorem union_discrepancy_of_seed (p : V → Fin 4) (J : SimpleGraph V)
    [DecidableRel J.Adj] (R : Finset (Sym2 V)) (φ : Finset V → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hcross : ∀ x y, J.Adj x y → p x ≠ p y)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε)
    (m₀ : ℕ) (hm : 2 * ε * J.edgeFinset.card ≤ (m₀ : ℝ)) :
    ∀ i j, (pool (category p) (R ∪ J.edgeFinset) i).card ≤
      (pool (category p) (R ∪ J.edgeFinset) j).card + (m₀ + R.card) := by
  apply union_discrepancy
  intro i j
  have hh := (abs_le.mp (category_difference p J φ ε hε hcross hload i j)).2
  have hr : ((pool (category p) J.edgeFinset i).card : ℝ) ≤
      (pool (category p) J.edgeFinset j).card + m₀ := by linarith
  exact_mod_cast hr

/-- Remove both abstract category-count assumptions of Stage120 using the
child seed, the size of the protected reserve, and actual neighbour witnesses. -/
theorem exists_recut_of_seed_and_neighbours (p : V → Fin 4)
    (E R : Finset (Sym2 V)) (J : SimpleGraph V) [DecidableRel J.Adj]
    (hRJ : Disjoint R J.edgeFinset)
    (hcross : ∀ x y, s(x, y) ∈ R ∪ J.edgeFinset → p x ≠ p y)
    (hE : ∀ k : Fin 2, bal p k E = 0)
    (φ : Finset V → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε)
    (m₀ D P : ℕ) (hm : 2 * ε * J.edgeFinset.card ≤ (m₀ : ℝ))
    (hP : m₀ + R.card < P) (hdeg : ∀ v, incidentLoad J.edgeFinset v ≤ D)
    (A : Fin 3 → Finset V) (B : Fin 3 → V → Finset V) (b : Fin 3 → ℕ)
    (hB : ∀ i u, u ∈ A i → b i ≤ (B i u).card)
    (hout : ∀ i u, u ∈ A i → ∀ v ∈ B i u, v ∉ A i)
    (hedge : ∀ i u, u ∈ A i → ∀ v ∈ B i u,
      s(u, v) ∈ pool (category p) J.edgeFinset i)
    (hsize : ∀ i, P ≤ (A i).card * b i) :
    ∃ Y ⊆ J.edgeFinset, Disjoint Y R ∧ Y.card ≤ 2 * (m₀ + R.card) ∧
      (∀ v, incidentLoad Y v ≤ 3 * quota (m₀ + R.card) D P) ∧
      (∀ k : Fin 2, bal p k ((R ∪ J.edgeFinset) \ Y) = 0) ∧
      ∀ S : Finset (Sym2 V), Disjoint S (R ∪ J.edgeFinset) →
        S ∪ (R ∪ J.edgeFinset) ⊆ E → HasDecomp p F3 (Y ∪ S) →
        ∀ k : Fin 2,
          bal p k (E \ ((Y ∪ S) ∪ (R ∪ (J.edgeFinset \ Y)))) = 0 := by
  have hp := union_discrepancy_of_seed p J R φ ε hε
    (fun x y h => hcross x y (mem_union_right R (SimpleGraph.mem_edgeFinset.mpr h)))
    hload m₀ hm
  have hc : ∀ i, P ≤ (pool (category p) J.edgeFinset i).card := by
    intro i
    exact (hsize i).trans (pool_card_lower _ (A i) (B i) (b i)
      (hB i) (hout i) (hedge i))
  exact exists_reserve_aware_recut p E R J.edgeFinset (m₀ + R.card) D P
    hRJ hcross hE hP hdeg hp hc

end PartitionedTriangleAbsorption.ReserveChargeStage121
