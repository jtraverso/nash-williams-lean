/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests

/-! # Degree concentration when complete triangles are selected

The degree at a fixed vertex is twice the number of selected incident blocks.
The packing property bounds the number of incident blocks by half the order.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {m : ℕ}

def blockCount (s : Finset (Fin m)) (x : Fin m → Bool) : ℝ :=
  ∑ i ∈ s, if x i then 1 else 0

theorem blockCount_mean (ρ : ℝ) (s : Finset (Fin m)) :
    cubeMean (fun _ : Fin m => ρ) (blockCount s) = ρ * s.card := by
  unfold blockCount
  rw [cubeMean_sum]
  simp only [cubeMean_coord, sum_const, nsmul_eq_mul]
  ring

theorem blockCount_eq_pairCount (s : Finset (Fin m)) (x : Fin m → Bool) :
    blockCount s x = pairCount s id id x := by
  unfold blockCount pairCount pairIndicator
  simp only [id_eq, and_self]

theorem blockCount_coordinate (s : Finset (Fin m)) :
    CoordBounded (blockCount s) (fun i => if i ∈ s then 1 else 0) := by
  intro i x
  rw [blockCount_eq_pairCount, blockCount_eq_pairCount]
  have h := pairCount_coordinate s id id i x
  by_cases hi : i ∈ s <;> simpa [or_self, filter_eq', hi] using h

theorem blockCount_upper_tail (s : Finset (Fin m)) (ρ n : ℝ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hn : 0 < n) (hs : 2 * (s.card : ℝ) ≤ n) :
    cubeProb (fun _ : Fin m => ρ) (fun x => ρ * n < blockCount s x) ≤
      Real.exp (-(ρ * n / 8)) := by
  classical
  let c : Fin m → ℝ := fun i => if i ∈ s then 1 else 0
  let u : ℝ := ρ * n / 2
  have hu : 0 < u := by dsimp [u]; positivity
  have hq : ∀ _i : Fin m, 0 ≤ ρ ∧ ρ ≤ 1 := fun _ => ⟨hρ.le, hρ1⟩
  have hc : ∀ i, 0 ≤ c i ∧ c i ≤ 1 := by
    intro i
    dsimp [c]
    split_ifs <;> norm_num
  have hmean : cubeMean (fun _ : Fin m => ρ) (blockCount s) ≤ ρ * n / 2 := by
    rw [blockCount_mean]
    have hh := mul_le_mul_of_nonneg_left hs hρ.le
    linarith only [hh]
  have hvarEq : (∑ i : Fin m, ρ * c i ^ 2) = ρ * s.card := by
    simp [c, mul_ite, sum_ite_mem, nsmul_eq_mul, mul_comm]
  have hvar : (∑ i : Fin m, ρ * c i ^ 2) ≤ ρ * n / 2 := by
    rw [hvarEq]
    have hh := mul_le_mul_of_nonneg_left hs hρ.le
    linarith only [hh]
  have hvar0 : 0 ≤ ∑ i : Fin m, ρ * c i ^ 2 := by rw [hvarEq]; positivity
  have hsub : ∀ x, ρ * n < blockCount s x →
      u ≤ blockCount s x - cubeMean (fun _ : Fin m => ρ) (blockCount s) := by
    intro x hx
    dsimp [u]
    linarith only [hx, hmean]
  have hden : 0 < 2 * ((∑ i : Fin m, ρ * c i ^ 2) + 1 * u) := by
    linarith only [hu, hvar0]
  have hdenupper : 2 * ((∑ i : Fin m, ρ * c i ^ 2) + 1 * u) ≤ 2 * ρ * n := by
    dsimp [u]
    linarith only [hvar]
  have hratio : ρ * n / 8 ≤
      u ^ 2 / (2 * ((∑ i : Fin m, ρ * c i ^ 2) + 1 * u)) := by
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ (ρ * n / 8) * (2 * ρ * n) :=
        mul_le_mul_of_nonneg_left hdenupper (by positivity)
      _ = u ^ 2 := by dsimp [u]; ring
  calc
    _ ≤ cubeProb (fun _ : Fin m => ρ)
        (fun x => u ≤ blockCount s x - cubeMean (fun _ : Fin m => ρ) (blockCount s)) :=
      cubeProb_mono _ hq hsub
    _ ≤ Real.exp (-(u ^ 2 / (2 * ((∑ i : Fin m, ρ * c i ^ 2) + 1 * u)))) :=
      cube_upper_tail _ hq _ c 1 (by norm_num) hc (blockCount_coordinate s) u hu
    _ ≤ _ := Real.exp_le_exp.mpr (neg_le_neg hratio)

#print axioms blockCount_mean
#print axioms blockCount_coordinate
#print axioms blockCount_upper_tail

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests
