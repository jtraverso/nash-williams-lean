/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ApproximateBalanceStage114
public import PartitionedTriangleAbsorption.NeighbourPoolCapacityStage114

/-! # Trimming with a computed degree quota

Approximate loads determine the surplus bound, actual neighbour witnesses
give mutable pool sizes, and integer division chooses a sufficient quota.
The witnesses still have to come from the reserve construction.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.SeedDrivenTrimStage114

open Finset AntiEdgeSelection TypedNibble TypedApplicationLinks TypedLoadNecessity
  CoverDownStage105 F3ReserveTrimStage109 ReserveTrimStage109
  ApproximateBalanceStage114 NeighbourPoolCapacityStage114

def quota (m D P : ℕ) : ℕ := 2 * m * D / (P - m) + 1

theorem quota_capacity (m D P : ℕ) (hP : m < P) :
    2 * m * D + m * quota m D P < quota m D P * P := by
  have hd : 0 < P - m := Nat.sub_pos_of_lt hP
  have h := (Nat.div_lt_iff_lt_mul hd).mp (Nat.lt_succ_self (2 * m * D / (P - m)))
  have hp := Nat.sub_add_cancel hP.le
  change 2 * m * D < quota m D P * (P - m) at h
  calc
    2 * m * D + m * quota m D P <
        quota m D P * (P - m) + m * quota m D P := Nat.add_lt_add_right h _
    _ = quota m D P * P := by rw [Nat.mul_comm m, ← Nat.mul_add, hp]

/-- An independently allocated quota can bound the computed one without
introducing a new selector assumption. -/
theorem quota_le (m D P q : ℕ) (hP : m < P)
    (hbudget : 2 * m * D < q * (P - m)) : quota m D P ≤ q := by
  have h := (Nat.div_lt_iff_lt_mul (Nat.sub_pos_of_lt hP)).mpr hbudget
  exact h

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exists_trim_of_seed_and_neighbours
    (p : V → Fin 4) (J : SimpleGraph V) [DecidableRel J.Adj]
    (X R : Finset (Sym2 V)) (hhost : X ∪ R = J.edgeFinset)
    (φ : Finset V → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hload : ∀ e ∈ J.edgeFinset, |edgeLoad p F3 J φ e - 1| ≤ ε)
    (hcross : ∀ u v, J.Adj u v → p u ≠ p v)
    (m D P : ℕ) (hm : 2 * ε * J.edgeFinset.card ≤ (m : ℝ)) (hP : m < P)
    (hdeg : ∀ v, incidentLoad R v ≤ D)
    (A : Fin 3 → Finset V) (B : Fin 3 → V → Finset V) (b : Fin 3 → ℕ)
    (hB : ∀ i u, u ∈ A i → b i ≤ (B i u).card)
    (hout : ∀ i u, u ∈ A i → ∀ v ∈ B i u, v ∉ A i)
    (hedge : ∀ i u, u ∈ A i → ∀ v ∈ B i u,
      s(u, v) ∈ pool (category p) (R \ X) i)
    (hsize : ∀ i, P ≤ (A i).card * b i) :
    ∃ Y ⊆ R \ X, (∀ v, incidentLoad Y v ≤ 3 * quota m D P) ∧
      ∀ k : Fin 2, bal p k (J.edgeFinset \ Y) = 0 := by
  let a := fun i => (pool (category p) J.edgeFinset i).card
  let t := min (a 0) (min (a 1) (a 2))
  have hpair : ∀ i j, a i ≤ a j + m := by
    intro i j
    have h := (abs_le.mp (category_difference p J φ ε hε hcross hload i j)).2
    have hr : (a i : ℝ) ≤ a j + m := by dsimp [a]; linarith
    exact_mod_cast hr
  have ht : ∀ i, t ≤ a i := by
    intro i
    fin_cases i <;> dsimp [t] <;> omega
  have hsurplus : ∀ i, a i - t ≤ m := by
    intro i
    have h0 := hpair i 0
    have h1 := hpair i 1
    have h2 := hpair i 2
    dsimp [t]
    omega
  have hpools : ∀ i, P ≤ (pool (category p) (R \ X) i).card := by
    intro i
    exact (hsize i).trans (pool_card_lower _ (A i) (B i) (b i)
      (hB i) (hout i) (hedge i))
  have hcap : ∀ i, let M := (pool (category p) (X ∪ R) i).card - t
      M = 0 ∨ 2 * M * D + M * quota m D P <
        quota m D P * (pool (category p) (R \ X) i).card := by
    intro i
    right
    rw [hhost]
    have hs := hsurplus i
    have hsmall : 2 * (a i - t) * D + (a i - t) * quota m D P ≤
        2 * m * D + m * quota m D P := by gcongr
    exact hsmall.trans_lt ((quota_capacity m D P hP).trans_le
      (Nat.mul_le_mul_left _ (hpools i)))
  obtain ⟨Y, hY, hYdeg, hbal⟩ := exists_balanced_trim p X R t (quota m D P) D
    (fun u v he => hcross u v (SimpleGraph.mem_edgeFinset.mp (hhost ▸ he))) hdeg
    (fun i => by rw [hhost]; exact ht i) hcap
  refine ⟨Y, hY, hYdeg, ?_⟩
  simpa only [hhost] using hbal

end PartitionedTriangleAbsorption.SeedDrivenTrimStage114
