/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedNibble.Nibble.CubeTools

/-! # Two-block tests in a Bernoulli-selected triangle packing

A common-neighbour witness survives when one or two prescribed blocks are
selected.  These expectations and coordinate bounds include the case where
both edges belong to the same block.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {m : ℕ}

def pairIndicator (a b : Fin m) (x : Fin m → Bool) : ℝ :=
  if x a = true ∧ x b = true then 1 else 0

theorem pairIndicator_nonneg (a b : Fin m) (x : Fin m → Bool) :
    0 ≤ pairIndicator a b x := by unfold pairIndicator; split_ifs <;> norm_num

theorem pairIndicator_le_one (a b : Fin m) (x : Fin m → Bool) :
    pairIndicator a b x ≤ 1 := by unfold pairIndicator; split_ifs <;> norm_num

theorem pairIndicator_mean (ρ : ℝ) (a b : Fin m) :
    cubeMean (fun _ => ρ) (pairIndicator a b) = if a = b then ρ else ρ ^ 2 := by
  by_cases hab : a = b
  · subst b
    simp only [ite_true]
    change cubeMean (fun _ : Fin m => ρ)
      (fun x => if x a = true ∧ x a = true then 1 else 0) = ρ
    simpa only [and_self] using cubeMean_coord (fun _ : Fin m => ρ) a
  · rw [ite_eq_right hab]
    have hprod (x : Fin m → Bool) : pairIndicator a b x =
        (if x a then (1 : ℝ) else 0) * (if x b then (1 : ℝ) else 0) := by
      cases ha : x a <;> cases hb : x b <;> simp [pairIndicator, ha, hb]
    rw [cubeMean_congr (fun _ : Fin m => ρ) hprod]
    have hind : IndepOf {a} (fun x : Fin m → Bool => if x b then (1 : ℝ) else 0) := by
      intro x j c hj
      rw [mem_singleton.mp hj]
      dsimp only
      rw [Function.update_of_ne (Ne.symm hab)]
    rw [cubeMean_coord_mul (fun _ : Fin m => ρ) a _ hind, cubeMean_coord]
    ring

theorem pairIndicator_mean_ge (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (a b : Fin m) :
    ρ ^ 2 ≤ cubeMean (fun _ => ρ) (pairIndicator a b) := by
  rw [pairIndicator_mean]
  split_ifs
  · nlinarith
  · rfl

def pairCount {W : Type*} (s : Finset W) (a b : W → Fin m) (x : Fin m → Bool) : ℝ :=
  ∑ w ∈ s, pairIndicator (a w) (b w) x

theorem pairCount_mean_ge {W : Type*} (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (s : Finset W) (a b : W → Fin m) :
    ρ ^ 2 * s.card ≤ cubeMean (fun _ => ρ) (pairCount s a b) := by
  unfold pairCount
  rw [cubeMean_sum]
  calc
    _ = ∑ _w ∈ s, ρ ^ 2 := by rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := sum_le_sum fun w _ => pairIndicator_mean_ge ρ hρ0 hρ1 (a w) (b w)

theorem pairIndicator_coordinate (a b i : Fin m) (x : Fin m → Bool) :
    |pairIndicator a b (Function.update x i true) -
      pairIndicator a b (Function.update x i false)| ≤ if a = i ∨ b = i then 1 else 0 := by
  by_cases hi : a = i ∨ b = i
  · rw [ite_eq_left hi, abs_le]
    have h1 := pairIndicator_nonneg a b (Function.update x i true)
    have h2 := pairIndicator_le_one a b (Function.update x i true)
    have h3 := pairIndicator_nonneg a b (Function.update x i false)
    have h4 := pairIndicator_le_one a b (Function.update x i false)
    constructor <;> linarith
  · have hai : a ≠ i := fun h => hi (Or.inl h)
    have hbi : b ≠ i := fun h => hi (Or.inr h)
    simp only [ite_eq_right hi, pairIndicator, Function.update_of_ne hai,
      Function.update_of_ne hbi, sub_self, abs_zero, le_refl]

theorem pairCount_coordinate {W : Type*} (s : Finset W) (a b : W → Fin m) :
    CoordBounded (pairCount s a b)
      (fun i => ((s.filter fun w => a w = i ∨ b w = i).card : ℝ)) := by
  classical
  intro i x
  unfold pairCount
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ w ∈ s, |pairIndicator (a w) (b w) (Function.update x i true) -
        pairIndicator (a w) (b w) (Function.update x i false)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ w ∈ s, if a w = i ∨ b w = i then (1 : ℝ) else 0 :=
      sum_le_sum fun w _ => pairIndicator_coordinate (a w) (b w) i x
    _ = _ := by simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

#print axioms pairIndicator_mean
#print axioms pairCount_mean_ge
#print axioms pairCount_coordinate

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble.ReserveTests
