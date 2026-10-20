/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.F0Direct.HostRealInverse
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.LocalProducer
public import PartitionedTriangleAbsorption.BlowupB.F0Direct.Closure

@[expose] public section

/-!
# Exact physical weights from the host hypotheses

This producer discharges the real-inverse argument in `Closure`: no
fractional weighting or inverse is assumed of the graph.
-/

namespace PartitionedTriangleAbsorption.BlowupB.F0Direct

open Finset TypedApplicationLinks

theorem weight_producer (a : ℝ) (ha : 0<a) :
    ∃ N : ℕ, WeightProducer a (localEpsilon a) N := by
  let θ := localTheta a
  let N : ℕ := ⌈4096/θ⌉₊+1
  have ht : 0<θ := localTheta_pos ha
  have he := localEpsilon_pos ha
  have he1 := localEpsilon_le ha
  have hsmall : 307200*localEpsilon a≤θ := by
    change 307200*(θ/(2:ℝ)^30)≤θ
    norm_num
    linarith only [ht]
  have hpositive : 14*(1024/(θ/100))*localEpsilon a≤1 := by
    change 14*(1024/(θ/100))*(θ/(2:ℝ)^30)≤1
    have hh : 14*(1024/(θ/100))*(θ/(2:ℝ)^30) =
        (1433600:ℝ)/(2:ℝ)^30 := by
      field_simp [ht.ne']
      <;> ring
    rw [hh]
    norm_num
  refine ⟨N,?_⟩
  intro V _ _ hn p G _ hG hdiv
  have hn0 : 0<Fintype.card V := by dsimp [N] at hn; omega
  have hn1 : ⌈4096/θ⌉₊≤Fintype.card V := by dsimp [N] at hn; omega
  have hn1R : (⌈4096/θ⌉₊:ℝ)≤Fintype.card V := by exact_mod_cast hn1
  have hscale : 4096≤θ*Fintype.card V := by
    have hh : 4096/θ≤(Fintype.card V:ℝ) := (Nat.le_ceil _).trans hn1R
    have hh' := (div_le_iff₀ ht).mp hh
    nlinarith only [hh']
  have hi := hG.balancedInverse he.le θ ht (localTheta_le a)
    (localTheta_scale a) hscale hsmall
  exact hG.exactWeights_of_inverse he.le (by linarith) hn0
    hpositive hdiv hi

#print axioms weight_producer

end PartitionedTriangleAbsorption.BlowupB.F0Direct
