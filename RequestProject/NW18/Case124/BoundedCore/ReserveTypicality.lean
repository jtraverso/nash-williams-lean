/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-! Preserve the cancellation between sampler monitors k1 and k2. Bounding
them separately by the whole child would waste the Dirac matching margin. -/

namespace NashWilliams18.Case124.BoundedCore

open Finset

variable {V : Type*}

/-- Subtract the sampled good-neighbour monitor from the sampled size monitor.
The error is twice the sampler error, not a fixed fraction of the target size. -/
theorem sampled_defect_bound (C R : Finset V) (good : V → Prop) [DecidablePred good]
    (ρ err : ℝ)
    (hsize : |(R.card : ℝ) - ρ * C.card| ≤ err)
    (hgood : |((R.filter good).card : ℝ) - ρ * (C.filter good).card| ≤ err) :
    ((R.filter (fun v => ¬ good v)).card : ℝ) ≤
      ρ * (C.filter (fun v => ¬ good v)).card + 2 * err := by
  have hr := card_filter_add_card_filter_not (s := R) good
  have hc := card_filter_add_card_filter_not (s := C) good
  have hr' : ((R.filter good).card : ℝ) + (R.filter (fun v => ¬ good v)).card = R.card :=
    by exact_mod_cast hr
  have hc' : ((C.filter good).card : ℝ) + (C.filter (fun v => ¬ good v)).card = C.card :=
    by exact_mod_cast hc
  have hupper := (abs_le.mp hsize).2
  have hlower := (abs_le.mp hgood).1
  have hcρ := congrArg (fun r : ℝ => ρ * r) hc'
  simp only [mul_add] at hcρ
  linarith

end NashWilliams18.Case124.BoundedCore

#print axioms NashWilliams18.Case124.BoundedCore.sampled_defect_bound
