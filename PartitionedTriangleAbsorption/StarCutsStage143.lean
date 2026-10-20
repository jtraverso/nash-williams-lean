/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.ThreeColumnTransportStage143
public import Mathlib.Algebra.BigOperators.Fin

/-! # Reduction of the eight cuts for genuine star degree inventories

The three global lower-column bounds remain explicit obligations. No physical
matching or preservation by exceptional pre-cleaning is asserted here.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StarCutsStage143

open Finset ThreeColumnTransportStage143

/-- The coupled three-class intervals leave demand no larger than any one
of the residual edge capacities. -/
theorem row_slack (a h : ℕ) (b : Fin 3 → ℕ)
    (hdeg : a + ∑ i, b i = 2 * h) (ha : a ≤ h) (hb : ∀ i, b i ≤ h) :
    let l := fun i => a + b i - h
    (∑ i, l i) ≤ a ∧
      ∀ i, l i ≤ b i ∧ (a - ∑ j, l j) ≤ b i - l i := by
  dsimp only
  have h0 := hb 0
  have h1 := hb 1
  have h2 := hb 2
  rw [Fin.sum_univ_three] at hdeg ⊢
  constructor
  · omega
  · intro i
    fin_cases i
    · change a + b 0 - h ≤ b 0 ∧
        a - (a + b 0 - h + (a + b 1 - h) + (a + b 2 - h)) ≤ b 0 - (a + b 0 - h)
      omega
    · change a + b 1 - h ≤ b 1 ∧
        a - (a + b 0 - h + (a + b 1 - h) + (a + b 2 - h)) ≤ b 1 - (a + b 1 - h)
      omega
    · change a + b 2 - h ≤ b 2 ∧
        a - (a + b 0 - h + (a + b 1 - h) + (a + b 2 - h)) ≤ b 2 - (a + b 2 - h)
      omega

/-- Every proper column cut has zero residual demand when each single
column can accommodate the residual row demand. -/
theorem cuts_of_single_column_slack {V : Type*} [Fintype V]
    (R : V → ℕ) (U : V → Fin 3 → ℕ) (C : Fin 3 → ℕ)
    (hrow : ∀ v i, R v ≤ U v i) (htotal : (∑ v, R v) ≤ ∑ i, C i)
    (J : Finset (Fin 3)) :
    (∑ v, (R v - ∑ i ∈ univ \ J, U v i)) ≤ ∑ i ∈ J, C i := by
  classical
  by_cases hj : J = univ
  · simpa [hj] using htotal
  · have hex : ∃ i : Fin 3, i ∉ J := by
      by_contra hn
      apply hj
      ext i
      simp only [mem_univ, iff_true]
      by_contra hi
      exact hn ⟨i, hi⟩
    obtain ⟨i, hi⟩ := hex
    have hz : ∀ v, (R v - ∑ j ∈ univ \ J, U v j) = 0 := by
      intro v
      apply Nat.sub_eq_zero_of_le
      exact (hrow v i).trans (single_le_sum (fun _ _ => Nat.zero_le _)
        (mem_sdiff.mpr ⟨mem_univ _, hi⟩))
    simp only [hz, sum_const_zero, Nat.zero_le]

/-- Once the three forced column loads and total demand are funded, all
eight cuts hold and the star counts have a natural-number allocation. -/
theorem exists_star_counts {V : Type*} [Fintype V]
    (a h : V → ℕ) (b : V → Fin 3 → ℕ) (q : Fin 3 → ℕ)
    (hdeg : ∀ v, a v + ∑ i, b v i = 2 * h v)
    (ha : ∀ v, a v ≤ h v) (hb : ∀ v i, b v i ≤ h v)
    (hforced : ∀ i, (∑ v, (a v + b v i - h v)) ≤ q i)
    (htotal : (∑ v, a v) ≤ ∑ i, q i) :
    ∃ x : V → Fin 3 → ℕ,
      (∀ v, ∑ i, x v i = a v) ∧
      (∀ v i, a v + b v i - h v ≤ x v i ∧ x v i ≤ b v i) ∧
      (∀ i, ∑ v, x v i ≤ q i) := by
  classical
  let l (v : V) (i : Fin 3) := a v + b v i - h v
  let R (v : V) := a v - ∑ i, l v i
  let U (v : V) (i : Fin 3) := b v i - l v i
  let C (i : Fin 3) := q i - ∑ v, l v i
  have hs (v : V) := row_slack (a v) (h v) (b v) (hdeg v) (ha v) (hb v)
  have hr : ∀ v i, R v ≤ U v i := fun v i => (hs v).2 i |>.2
  have haeq : (∑ v, R v) + ∑ v, ∑ i, l v i = ∑ v, a v := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    exact Nat.sub_add_cancel (hs v).1
  have hceq : (∑ i, C i) + ∑ v, ∑ i, l v i = ∑ i, q i := by
    rw [sum_comm, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    exact Nat.sub_add_cancel (hforced i)
  have ht : (∑ v, R v) ≤ ∑ i, C i := by omega
  obtain ⟨z, hzrow, hzcap, hzcol⟩ := exists_transport R U C
    (cuts_of_single_column_slack R U C hr ht)
  refine ⟨fun v i => l v i + z v i, ?_, ?_, ?_⟩
  · intro v
    rw [sum_add_distrib, hzrow]
    have hv := (hs v).1
    change (∑ i, l v i) ≤ a v at hv
    dsimp only [R]
    omega
  · intro v i
    have hl := (hs v).2 i |>.1
    change l v i ≤ b v i at hl
    have hu := hzcap v i
    dsimp only [U] at hu
    change l v i ≤ l v i + z v i ∧ l v i + z v i ≤ b v i
    omega
  · intro i
    rw [sum_add_distrib]
    have hc := hzcol i
    have hl := hforced i
    change (∑ v, l v i) ≤ q i at hl
    dsimp only [C] at hc
    omega

/-- Scalar certificate for the independent-root counting argument in a cut.
The graph-counting inequality `hroot` is still a separate obligation. -/
theorem forced_load_scalar (h0 h1 p0 p1 M m cut L : ℝ)
    (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1)
    (hroot : L ≤ M + (h0 - h1) * (p0 - p1) - p0 ^ 2 - p1 ^ 2 + p0 * p1)
    (hdensity : 3 * (h0 + h1) ^ 2 ≤ 8 * m)
    (hcut : cut + M = h0 * h1) :
    3 * L ≤ 2 * m - 3 * cut := by
  have hs := sq_nonneg ((h0 - h1) / 2 - p0 + p1)
  have hp := mul_nonneg hp0 hp1
  nlinarith

end PartitionedTriangleAbsorption.StarCutsStage143
