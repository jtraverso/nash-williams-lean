/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.FinitePackingRepair

/-! # The star-wise obligation missing from cardinality-only rounding

This module does not assert a new nibble theorem. It proves the deterministic
degree adapter and a finite simultaneous-outcome lemma for supplied moments.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.StarResidualControl

open Finset

variable {V : Type*} [DecidableEq V]

def star (B : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  B.filter (fun e => v ∈ e)

/-- Covered and residual physical edges partition each original vertex star. -/
theorem star_partition (B P : Finset (Sym2 V)) (v : V) :
    (star (B \ P) v).card + (star (B ∩ P) v).card = (star B v).card := by
  have hs : star (B \ P) v = star B v \ star P v := by
    ext e
    simp only [star, mem_filter, mem_sdiff]
    tauto
  have hi : star (B ∩ P) v = star B v ∩ star P v := by
    ext e
    simp only [star, mem_filter, mem_inter]
    tauto
  rw [hs, hi]
  exact card_sdiff_add_card_inter _ _

/-- Maximum residual degree is exactly the simultaneous star-coverage target. -/
theorem degBounded_iff_star_coverage (B P : Finset (Sym2 V)) (r : ℝ) :
    DegBounded (B \ P) r ↔ ∀ v, (star B v).card ≤ (star (B ∩ P) v).card + r := by
  constructor
  · intro h v
    have hp : ((star (B \ P) v).card : ℝ) + (star (B ∩ P) v).card = (star B v).card :=
      by exact_mod_cast star_partition B P v
    have hd := h v
    change ((star (B \ P) v).card : ℝ) ≤ r at hd
    linarith
  · intro h v
    have hp : ((star (B \ P) v).card : ℝ) + (star (B ∩ P) v).card = (star B v).card :=
      by exact_mod_cast star_partition B P v
    have hd := h v
    change ((star (B \ P) v).card : ℝ) ≤ r
    linarith

/-- A covariance bound restricted to a star uses its size, not all graph edges. -/
theorem restricted_covariance_sum (S : Finset V) (cov : V → V → ℝ) (q ε : ℝ)
    (hcov : ∀ u ∈ S, ∀ v ∈ S, cov u v ≤ (if u = v then q else 0) + ε) :
    (∑ u ∈ S, ∑ v ∈ S, cov u v) ≤ (S.card : ℝ) * q + (S.card : ℝ) ^ 2 * ε := by
  calc
    (∑ u ∈ S, ∑ v ∈ S, cov u v) ≤
        ∑ u ∈ S, ∑ v ∈ S, ((if u = v then q else 0) + ε) :=
      sum_le_sum (fun u hu => sum_le_sum (fun v hv => hcov u hu v hv))
    _ = (S.card : ℝ) * q + (S.card : ℝ) ^ 2 * ε := by
      have hi : ∀ u ∈ S, (∑ v ∈ S, ((if u = v then q else 0) + ε)) =
          q + (S.card : ℝ) * ε := by
        intro u hu
        rw [sum_add_distrib, sum_ite_eq, ite_eq_left hu, sum_const, nsmul_eq_mul]
      rw [sum_congr rfl hi, sum_const, nsmul_eq_mul]
      ring

omit [DecidableEq V] in
/-- The second moment of a restricted sum is its restricted covariance sum. -/
theorem restricted_second_moment_identity {Ω : Type*} [Fintype Ω]
    (S : Finset V) (p : Ω → ℝ) (dev : V → Ω → ℝ) :
    (∑ ω, p ω * (∑ v ∈ S, dev v ω) ^ 2) =
      ∑ u ∈ S, ∑ v ∈ S, ∑ ω, p ω * dev u ω * dev v ω := by
  simp_rw [sq, sum_mul_sum, mul_sum, ← mul_assoc]
  rw [sum_comm]
  apply sum_congr rfl
  intro u _
  rw [sum_comm]

/-- This is the star-local analogue of the existing covered-count variance bound. -/
theorem restricted_second_moment_bound {Ω : Type*} [Fintype Ω]
    (S : Finset V) (p : Ω → ℝ) (dev : V → Ω → ℝ) (q ε : ℝ)
    (hcov : ∀ u ∈ S, ∀ v ∈ S,
      (∑ ω, p ω * dev u ω * dev v ω) ≤ (if u = v then q else 0) + ε) :
    (∑ ω, p ω * (∑ v ∈ S, dev v ω) ^ 2) ≤
      (S.card : ℝ) * q + (S.card : ℝ) ^ 2 * ε := by
  rw [restricted_second_moment_identity]
  exact restricted_covariance_sum S (fun u v => ∑ ω, p ω * dev u ω * dev v ω) q ε hcov

/-- Finite simultaneous concentration: the total second moment below t²
produces one outcome good at every index. No independence is assumed here. -/
theorem exists_simultaneous_of_second_moment
    {I Ω : Type*} [Fintype I] [Fintype Ω]
    (p : Ω → ℝ) (dev : I → Ω → ℝ) (t : ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hs : ∑ ω, p ω = 1) (ht : 0 < t)
    (hm : (∑ ω, p ω * ∑ i, (dev i ω) ^ 2) < t ^ 2) :
    ∃ ω, ∀ i, |dev i ω| < t := by
  classical
  by_contra hn
  push Not at hn
  have hb : ∀ ω, t ^ 2 ≤ ∑ i, (dev i ω) ^ 2 := by
    intro ω
    obtain ⟨i, hi⟩ := hn ω
    have hsq : t ^ 2 ≤ (dev i ω) ^ 2 := by
      nlinarith [sq_abs (dev i ω), abs_nonneg (dev i ω)]
    exact hsq.trans (single_le_sum (fun j _ => sq_nonneg (dev j ω)) (mem_univ i))
  have htotal : t ^ 2 ≤ ∑ ω, p ω * ∑ i, (dev i ω) ^ 2 := by
    calc
      t ^ 2 = ∑ ω, p ω * t ^ 2 := by rw [← sum_mul, hs, one_mul]
      _ ≤ ∑ ω, p ω * ∑ i, (dev i ω) ^ 2 :=
        sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hb ω) (hp ω))
  linarith

/-- The conservative Chebyshev union estimate cannot certify per-round
star error below half the progress scale. This does not refute existence. -/
theorem conservative_budget_obstruction (n θ t ε : ℝ)
    (hn : 0 < n) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ht : 0 < t)
    (htop : t ≤ θ * n / 2) (hε : 0 ≤ ε) :
    4 ≤ (n ^ 2 * θ + n ^ 3 * ε) / t ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos ht)).mpr
  have hs : 4 * t ^ 2 ≤ (θ * n) ^ 2 := by nlinarith
  have hsq : θ ^ 2 ≤ θ := by nlinarith
  have hm := mul_le_mul_of_nonneg_right hsq (sq_nonneg n)
  have he : 0 ≤ n ^ 3 * ε := mul_nonneg (pow_nonneg hn.le 3) hε
  nlinarith

end PartitionedTriangleAbsorption.StarResidualControl
