/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.MetricSpace.CauSeqFilter
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Tactic

/-!
# The small real exponential series from its defining Cauchy sequence

This supplies exactly the series identity needed by the finite Bernoulli
estimate. It uses no differentiation of Banach-algebra exponentials.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedNibble

open Finset Filter
open scoped Topology

theorem real_exp_hasSum_small (x : ℝ) (hx : |x| < 1) :
    HasSum (fun k : ℕ => x ^ k / (k.factorial : ℝ)) (Real.exp x) := by
  have hcomp (k : ℕ) : ‖x ^ k / (k.factorial : ℝ)‖ ≤ |x| ^ k := by
    rw [Real.norm_eq_abs, abs_div, abs_pow,
      abs_of_pos (show (0 : ℝ) < k.factorial by positivity)]
    exact div_le_self (pow_nonneg (abs_nonneg x) k)
      (by exact_mod_cast (show 1 ≤ k.factorial from Nat.factorial_pos k))
  have hnorm : Summable (fun k : ℕ => ‖x ^ k / (k.factorial : ℝ)‖) :=
    (summable_geometric_of_lt_one (abs_nonneg x) hx).of_norm_bounded
      (fun k => by simpa only [norm_norm] using hcomp k)
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).mpr
  have hc : Tendsto (fun N : ℕ => ∑ k ∈ range N, (x : ℂ) ^ k / (k.factorial : ℂ))
      atTop (𝓝 (Complex.exp (x : ℂ))) := by
    rw [Complex.exp]
    exact (Complex.exp' (x : ℂ)).tendsto_limit
  have hr := (Complex.continuous_re.tendsto (Complex.exp (x : ℂ))).comp hc
  simpa only [Real.exp, Function.comp_def, Complex.re_sum, ← Complex.ofReal_pow,
    ← Complex.ofReal_natCast, ← Complex.ofReal_div, Complex.ofReal_re] using hr

#print axioms real_exp_hasSum_small

end PartitionedTriangleAbsorption.BlowupB.PaddedNibble
