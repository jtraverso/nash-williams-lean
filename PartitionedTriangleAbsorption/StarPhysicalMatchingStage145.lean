/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.PrescribedPhysicalPairingStage145
public import PartitionedTriangleAbsorption.StarPairProfileStage145
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Physical realization of an allocated star inventory

The relation may already exclude base edges used by earlier centres.
The root class is numbered zero, with the other classes numbered one to three.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StarPhysicalMatchingStage145

open Finset StarPairProfileStage145 PrescribedPhysicalPairingStage145

/-- A degree bound and a uniform class upper bound exclude two small classes. -/
theorem pair_has_large_class (c : Fin 4 → ℕ) (d L D : ℕ)
    (hdegree : d ≤ ∑ j, c j) (hupper : ∀ j, c j ≤ L)
    (hmargin : 2 * L + 4 * D + 2 < d) (j k : Fin 4) (hjk : j ≠ k) :
    2 * D + 1 < c j ∨ 2 * D + 1 < c k := by
  let s : Finset (Fin 4) := (univ.erase j).erase k
  have hk : k ∈ univ.erase j := by simp [hjk.symm]
  have hcard : s.card = 2 := by simp [s, card_erase_of_mem hk]
  have hrest : (∑ i ∈ s, c i) ≤ 2 * L := by
    calc
      (∑ i ∈ s, c i) ≤ ∑ _i ∈ s, L := sum_le_sum fun i _ => hupper i
      _ = 2 * L := by simp [hcard]
  have heq : (∑ i, c i) = c j + c k + ∑ i ∈ s, c i := by
    have h0 := sum_erase_add (univ : Finset (Fin 4)) c (mem_univ j)
    have h1 := sum_erase_add (univ.erase j) c hk
    dsimp only [s]
    omega
  omega

/-- Construct all pairs of one star, including the exact own-class quotas. -/
theorem exists_star_pairing {W : Type*} [Fintype W]
    (R : W → W → Prop) [DecidableRel R] (hsym : ∀ u v, R u v → R v u)
    (p : W → Fin 4) (a h : ℕ) (b x : Fin 3 → ℕ)
    (hdeg : a + ∑ i, b i = 2 * h) (ha : a ≤ h)
    (hrow : ∑ i, x i = a)
    (hx : ∀ i, a + b i - h ≤ x i ∧ x i ≤ b i)
    (hcounts : ∀ j, (univ.filter fun v => p v = j).card = classSize a b j)
    (D : ℕ)
    (hmiss : ∀ v, (univ.filter fun w => p w ≠ p v ∧ ¬ R v w).card ≤ D)
    (hlarge : ∀ j k, j ≠ k →
      2 * D + 1 < classSize a b j ∨ 2 * D + 1 < classSize a b k) :
    ∃ f : W ≃ W, Function.Involutive f ∧ (∀ v, p (f v) ≠ p v) ∧
      (∀ v, R v (f v)) ∧
      (∀ j k, (univ.filter fun v => p v = j ∧ p (f v) = k).card =
        pairDemand a h b x j k) ∧
      (univ.filter fun v => p v = 0 ∧ p (f v) = 1).card = x 0 ∧
      (univ.filter fun v => p v = 0 ∧ p (f v) = 2).card = x 1 ∧
      (univ.filter fun v => p v = 0 ∧ p (f v) = 3).card = x 2 := by
  classical
  obtain ⟨f, hf, hc, hp, ht⟩ := exists_prescribed_physical_pairing R hsym p
    (pairDemand a h b x) (pairDemand_symm a h b x) (pairDemand_diag a h b x)
    (fun j => (pairDemand_rows a h b x hdeg ha hrow hx j).trans (hcounts j).symm)
    D hmiss (by simpa only [hcounts] using hlarge)
  refine ⟨f, hf, hc, hp, ht, ?_, ?_, ?_⟩
  · simpa [pairDemand] using ht 0 1
  · simpa [pairDemand] using ht 0 2
  · simpa [pairDemand] using ht 0 3

/-- The class-size tests follow from the degree margin; no pairwise supply
tests or supplied matching are required as input. -/
theorem exists_star_pairing_of_degree {W : Type*} [Fintype W]
    (R : W → W → Prop) [DecidableRel R] (hsym : ∀ u v, R u v → R v u)
    (p : W → Fin 4) (a h : ℕ) (b x : Fin 3 → ℕ)
    (hdeg : a + ∑ i, b i = 2 * h) (ha : a ≤ h)
    (hrow : ∑ i, x i = a)
    (hx : ∀ i, a + b i - h ≤ x i ∧ x i ≤ b i)
    (hcounts : ∀ j, (univ.filter fun v => p v = j).card = classSize a b j)
    (L D : ℕ) (hupper : ∀ j, classSize a b j ≤ L)
    (hmargin : 2 * L + 4 * D + 2 < 2 * h)
    (hmiss : ∀ v, (univ.filter fun w => p w ≠ p v ∧ ¬ R v w).card ≤ D) :
    ∃ f : W ≃ W, Function.Involutive f ∧ (∀ v, p (f v) ≠ p v) ∧
      (∀ v, R v (f v)) ∧
      (∀ j k, (univ.filter fun v => p v = j ∧ p (f v) = k).card =
        pairDemand a h b x j k) ∧
      (univ.filter fun v => p v = 0 ∧ p (f v) = 1).card = x 0 ∧
      (univ.filter fun v => p v = 0 ∧ p (f v) = 2).card = x 1 ∧
      (univ.filter fun v => p v = 0 ∧ p (f v) = 3).card = x 2 := by
  have hc : ∑ j, classSize a b j = 2 * h := by
    simpa [Fin.sum_univ_four, Fin.sum_univ_three, classSize, Nat.add_assoc] using hdeg
  exact exists_star_pairing R hsym p a h b x hdeg ha hrow hx hcounts D hmiss
    (pair_has_large_class (classSize a b) (2 * h) L D hc.ge hupper hmargin)

end PartitionedTriangleAbsorption.StarPhysicalMatchingStage145
