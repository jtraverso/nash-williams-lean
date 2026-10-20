/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.Nibble.CubeTools

/-! # BlowupB.CubeBlocks — block counts on the Bernoulli cube

For a finite family of blocks `B z ⊆ Fin m` (`z ∈ K`), the block count
`blockCount K B ω = #{z ∈ K : every coin of B z is true}` has mean `∑_z ∏_{i ∈ B z} q i`,
changes by at most `#{z ∈ K : i ∈ B z}` when coin `i` is flipped, and therefore obeys the
two-sided rare-coordinate Bernstein bound of `BernoulliConcentration`. Degrees, codegrees and
common neighbourhoods of a random subgraph are block counts.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB

open Finset BernoulliExposure BernoulliConcentration Nibble

variable {m : ℕ}

/-- Indicator of a coin. -/
def coin (ω : Fin m → Bool) (i : Fin m) : ℝ := if ω i then 1 else 0

theorem coin_nonneg (ω : Fin m → Bool) (i : Fin m) : 0 ≤ coin ω i := by
  unfold coin; split_ifs <;> norm_num

theorem coin_le_one (ω : Fin m → Bool) (i : Fin m) : coin ω i ≤ 1 := by
  unfold coin; split_ifs <;> norm_num

theorem prod_coin_nonneg (ω : Fin m → Bool) (I : Finset (Fin m)) : 0 ≤ ∏ i ∈ I, coin ω i :=
  prod_nonneg fun i _ => coin_nonneg ω i

theorem prod_coin_le_one (ω : Fin m → Bool) (I : Finset (Fin m)) : ∏ i ∈ I, coin ω i ≤ 1 :=
  prod_le_one₀ (fun i _ => coin_nonneg ω i) fun i _ => coin_le_one ω i

theorem prod_coin_update_of_notMem (ω : Fin m → Bool) {I : Finset (Fin m)} {j : Fin m}
    (hj : j ∉ I) (b : Bool) :
    ∏ i ∈ I, coin (Function.update ω j b) i = ∏ i ∈ I, coin ω i := by
  refine prod_congr rfl fun i hi => ?_
  have hij : i ≠ j := fun h => hj (h ▸ hi)
  simp only [coin, Function.update_of_ne hij]

/-- The mean of a product of distinct coins. -/
theorem cubeMean_prod_coin (q : Fin m → ℝ) (I : Finset (Fin m)) :
    cubeMean q (fun ω => ∏ i ∈ I, coin ω i) = ∏ i ∈ I, q i := by
  induction I using Finset.induction_on with
  | empty => simp only [prod_empty]; exact cubeMean_const q 1
  | insert a I ha ih =>
    rw [prod_insert ha]
    rw [cubeMean_congr q (g := fun ω => (if ω a then (1 : ℝ) else 0) * ∏ i ∈ I, coin ω i)
      (fun ω => by rw [prod_insert ha]; rfl)]
    rw [cubeMean_coord_mul q a _ (fun ω j b hj => by
      rw [mem_singleton] at hj
      subst hj
      exact prod_coin_update_of_notMem ω ha b), ih]

/-- Number of blocks all of whose coins are true. -/
def blockCount {ι : Type*} (K : Finset ι) (B : ι → Finset (Fin m)) (ω : Fin m → Bool) : ℝ :=
  ∑ z ∈ K, ∏ i ∈ B z, coin ω i

theorem cubeMean_blockCount {ι : Type*} (q : Fin m → ℝ) (K : Finset ι) (B : ι → Finset (Fin m)) :
    cubeMean q (blockCount K B) = ∑ z ∈ K, ∏ i ∈ B z, q i := by
  unfold blockCount
  rw [cubeMean_sum]
  exact sum_congr rfl fun z _ => cubeMean_prod_coin q (B z)

/-- Load of coin `i`: the number of blocks containing it. -/
def coinLoad {ι : Type*} (K : Finset ι) (B : ι → Finset (Fin m)) (i : Fin m) : ℝ :=
  ((K.filter fun z => i ∈ B z).card : ℝ)

theorem coordBounded_blockCount {ι : Type*} (K : Finset ι) (B : ι → Finset (Fin m)) :
    CoordBounded (blockCount K B) (coinLoad K B) := by
  classical
  intro i ω
  unfold blockCount coinLoad
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_le_sum fun z _ => ?_
  split_ifs with hz
  · rw [Nat.cast_one, abs_sub_le_iff]
    constructor
    · linarith [prod_coin_le_one (Function.update ω i true) (B z),
        prod_coin_nonneg (Function.update ω i false) (B z)]
    · linarith [prod_coin_le_one (Function.update ω i false) (B z),
        prod_coin_nonneg (Function.update ω i true) (B z)]
  · rw [prod_coin_update_of_notMem ω hz, prod_coin_update_of_notMem ω hz, sub_self, abs_zero]

/-- **Two-sided tail for block counts.** If every coin lies in at most `L` blocks, then
`P(|Y - EY| ≥ s) ≤ 2 exp(-s² / (2 (V + L s)))` with `V = ∑ qᵢ loadᵢ²`. -/
theorem blockCount_tail {ι : Type*} (q : Fin m → ℝ) (hq : ∀ i, 0 ≤ q i ∧ q i ≤ 1)
    (K : Finset ι) (B : ι → Finset (Fin m)) (L : ℝ) (hL : 0 < L)
    (hload : ∀ i, coinLoad K B i ≤ L) (s : ℝ) (hs : 0 < s) :
    cubeProb q (fun ω => s ≤ |blockCount K B ω - ∑ z ∈ K, ∏ i ∈ B z, q i|) ≤
      2 * Real.exp (-(s ^ 2 / (2 * ((∑ i, q i * coinLoad K B i ^ 2) + L * s)))) := by
  have hc : ∀ i, 0 ≤ coinLoad K B i ∧ coinLoad K B i ≤ L :=
    fun i => ⟨Nat.cast_nonneg _, hload i⟩
  have hU := cube_upper_tail q hq (blockCount K B) (coinLoad K B) L hL hc
    (coordBounded_blockCount K B) s hs
  have hD := cube_lower_tail q hq (blockCount K B) (coinLoad K B) L hL hc
    (coordBounded_blockCount K B) s hs
  rw [cubeMean_blockCount] at hU hD
  calc cubeProb q (fun ω => s ≤ |blockCount K B ω - ∑ z ∈ K, ∏ i ∈ B z, q i|)
      ≤ cubeProb q (fun ω => s ≤ blockCount K B ω - ∑ z ∈ K, ∏ i ∈ B z, q i ∨
          s ≤ (∑ z ∈ K, ∏ i ∈ B z, q i) - blockCount K B ω) :=
        cubeProb_mono q hq fun ω h => by
          rcases le_abs'.mp h with h' | h'
          · right; linarith
          · left; exact h'
    _ ≤ _ := (cubeProb_or_le q hq _ _).trans (by linarith)

end PartitionedTriangleAbsorption.BlowupB
