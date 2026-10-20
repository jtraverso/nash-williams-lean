/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalChains

@[expose] public section

/-! # Size estimates for transferring the complete signed inverse -/

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {t : ℕ}

omit [DecidableEq V] in
theorem total_mass_bound (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (M : ℝ) (hM : 0 ≤ M)
    (hz : ∀ T, IsCopy p F G T → |z T| ≤ M) :
    (∑ T ∈ copies p F G, |z T|) ≤ (Fintype.card V : ℝ) ^ 3 * M := by
  classical
  calc
    _ ≤ ∑ _T ∈ copies p F G, M := by
      apply sum_le_sum
      intro T hT
      exact hz T (PaddedNibble.TypedNibble.mem_copies_iff.mp hT)
    _ = ((copies p F G).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast copies_card_le_cube p F G) hM

theorem vertex_mass_bound (p : V → Fin t) (F : Finset (Multiset (Fin t)))
    (G : SimpleGraph V) (z : TriangleChain V) (M : ℝ) (hM : 0 ≤ M)
    (hz : ∀ T, IsCopy p F G T → |z T| ≤ M) (v : V) :
    (∑ T ∈ copies p F G with v ∈ T, |z T|) ≤ (Fintype.card V : ℝ) ^ 2 * M := by
  classical
  calc
    _ ≤ ∑ _T ∈ copies p F G with v ∈ _T, M := by
      apply sum_le_sum
      intro T hT
      exact hz T (PaddedNibble.TypedNibble.mem_copies_iff.mp (mem_filter.mp hT).1)
    _ = (((copies p F G).filter fun T => v ∈ T).card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast copies_through_card_le_square p F G v) hM

theorem transferred_inverse_bound (ε ω n : ℝ) (hε : 0 ≤ ε)
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : 0 < n) :
    9 * ε / (ω * n / 2) +
        81 * (n ^ 2 * ((2 : ℝ) ^ 20 * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 2 +
        108 * (n ^ 3 * ((2 : ℝ) ^ 20 * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 3 ≤
      ((2 : ℝ) ^ 32 / ω ^ 9) * ε / n := by
  have heq : 9 * ε / (ω * n / 2) +
        81 * (n ^ 2 * ((2 : ℝ) ^ 20 * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 2 +
        108 * (n ^ 3 * ((2 : ℝ) ^ 20 * ε / (ω ^ 6 * n))) / (ω * n / 2) ^ 3 =
      (18 * ω ^ 8 + 324 * (2 : ℝ) ^ 20 * ω + 864 * (2 : ℝ) ^ 20) * ε / (ω ^ 9 * n) := by
    field_simp
    ring
  have hp : ω ^ 8 ≤ 1 := pow_le_one₀ hω.le hω1
  have hc : 18 * ω ^ 8 + 324 * (2 : ℝ) ^ 20 * ω + 864 * (2 : ℝ) ^ 20 ≤
      (2 : ℝ) ^ 32 := by norm_num at *; linarith
  rw [heq]
  calc
    _ ≤ (2 : ℝ) ^ 32 * ε / (ω ^ 9 * n) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hc hε) (by positivity)
    _ = _ := by ring

theorem positive_repair_weights (ω n φ z : ℝ) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hn : 0 < n) (hlo : ω ^ 2 / n ≤ φ) (hhi : φ ≤ (27 / ω) / n)
    (hz : |z| ≤ (ω ^ 2 / 2) / n) :
    0 ≤ φ + z ∧ φ + z ≤ (54 / ω) / n := by
  have hloz := (abs_le.mp hz).1
  have hhiz := (abs_le.mp hz).2
  have hsq : ω ^ 2 ≤ 1 := pow_le_one₀ hω.le hω1
  have hsmall : ω ^ 2 / 2 ≤ 27 / ω := by
    apply (le_div_iff₀ hω).mpr
    have hm := mul_le_mul hsq hω1 hω.le (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hsmall' := div_le_div_of_nonneg_right hsmall hn.le
  have hnonneg : 0 ≤ (ω ^ 2 / 2) / n := by positivity
  have hdouble : ω ^ 2 / n = 2 * ((ω ^ 2 / 2) / n) := by ring
  have hdouble' : (54 / ω) / n = 2 * ((27 / ω) / n) := by ring
  constructor <;> linarith

#print axioms total_mass_bound
#print axioms vertex_mass_bound
#print axioms transferred_inverse_bound
#print axioms positive_repair_weights

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
