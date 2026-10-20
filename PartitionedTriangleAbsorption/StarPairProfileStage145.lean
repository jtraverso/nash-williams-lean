/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.FinCases

/-! # Exact pair demands for the physical star matching

Class zero is the centre's own class. The three allocated counts consume
the internal star edges; the remaining pairs use three distinct labels.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StarPairProfileStage145

open Finset

def pairDemand (a h : ℕ) (b x : Fin 3 → ℕ) (j k : Fin 4) : ℕ :=
  if j = 0 then
    if k = 1 then x 0 else if k = 2 then x 1 else if k = 3 then x 2 else 0
  else if k = 0 then
    if j = 1 then x 0 else if j = 2 then x 1 else if j = 3 then x 2 else 0
  else if j = k then 0
  else if j = 1 ∧ k = 2 ∨ j = 2 ∧ k = 1 then h - a - (b 2 - x 2)
  else if j = 1 ∧ k = 3 ∨ j = 3 ∧ k = 1 then h - a - (b 1 - x 1)
  else h - a - (b 0 - x 0)

def classSize (a : ℕ) (b : Fin 3 → ℕ) (j : Fin 4) : ℕ :=
  if j = 0 then a else if j = 1 then b 0 else if j = 2 then b 1 else b 2

/-- Residual neighbour counts satisfy the triangle inequalities exactly. -/
theorem residual_inventory (a h : ℕ) (b x : Fin 3 → ℕ)
    (hdeg : a + ∑ i, b i = 2 * h) (ha : a ≤ h)
    (hrow : ∑ i, x i = a)
    (hx : ∀ i, a + b i - h ≤ x i ∧ x i ≤ b i) :
    (∑ i, (b i - x i)) = 2 * (h - a) ∧
      ∀ i, b i - x i ≤ h - a := by
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  rw [Fin.sum_univ_three] at hdeg hrow ⊢
  constructor
  · omega
  · intro i
    have hi := hx i
    omega

theorem pairDemand_symm (a h : ℕ) (b x : Fin 3 → ℕ) (j k : Fin 4) :
    pairDemand a h b x j k = pairDemand a h b x k j := by
  fin_cases j <;> fin_cases k <;> simp [pairDemand]

theorem pairDemand_diag (a h : ℕ) (b x : Fin 3 → ℕ) (j : Fin 4) :
    pairDemand a h b x j j = 0 := by
  fin_cases j <;> simp [pairDemand]

/-- The six demands consume every neighbour exactly once. -/
theorem pairDemand_rows (a h : ℕ) (b x : Fin 3 → ℕ)
    (hdeg : a + ∑ i, b i = 2 * h) (ha : a ≤ h)
    (hrow : ∑ i, x i = a)
    (hx : ∀ i, a + b i - h ≤ x i ∧ x i ≤ b i)
    (j : Fin 4) : ∑ k, pairDemand a h b x j k = classSize a b j := by
  obtain ⟨hr, hb⟩ := residual_inventory a h b x hdeg ha hrow hx
  have h0 := hx 0
  have h1 := hx 1
  have h2 := hx 2
  have hb0 := hb 0
  have hb1 := hb 1
  have hb2 := hb 2
  rw [Fin.sum_univ_three] at hr hrow
  fin_cases j <;> simp [Fin.sum_univ_four, pairDemand, classSize] <;> omega

/-- Each allocated column is exactly the demand paired with the own class. -/
theorem own_class_demands (a h : ℕ) (b x : Fin 3 → ℕ) :
    pairDemand a h b x 0 1 = x 0 ∧
    pairDemand a h b x 0 2 = x 1 ∧
    pairDemand a h b x 0 3 = x 2 := by
  simp [pairDemand]

end PartitionedTriangleAbsorption.StarPairProfileStage145
