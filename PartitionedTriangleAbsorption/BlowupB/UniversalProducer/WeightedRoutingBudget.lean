/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.UniversalProducer.Refiner

@[expose] public section

/-! Arithmetic for routing a fixed virtual refiner with edge weights equal to
whole-library multiplicities. These lemmas do NOT assert existence of paths or
a refiner. The path-selection and subdivision assembly remain separate. -/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

/-- The apparent inverse-density loss is paid by the two-scale hierarchy. -/
theorem routing_density_cancellation (c lam rho omega : ℝ)
    (hc : 0 ≤ c) (hlam : 0 < lam) (hscale : rho ≤ c * lam ^ 2)
    (hsmall : lam ≤ c * omega) :
    rho / lam ≤ c ^ 2 * omega := by
  apply (div_le_iff₀ hlam).2
  calc
    rho ≤ c * lam ^ 2 := hscale
    _ = (c * lam) * lam := by ring
    _ ≤ (c * (c * omega)) * lam :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hc) hlam.le
    _ = c ^ 2 * omega * lam := by ring

/-- Supply beats weighted-heavy vertices, two blocked adjacency queries, and
the vertices already used by one path. K bounds old library incidence, L bounds
path length. The numerical constants intentionally retain ample slack. -/
theorem weighted_routing_choice_budget (K L lam rho omega n : ℝ)
    (hK : 1 ≤ K) (hL : 0 ≤ L) (hlam : 0 < lam) (hrho : 0 ≤ rho)
    (hn : 0 < n) (hsmall : 64 * K * lam ≤ omega)
    (hratio : 128 * L * rho ≤ omega * lam)
    (hrholam : rho ≤ lam) (horder : 4 * (L + 1) ≤ omega * n) :
    (21 * L * rho / lam) * n +
      2 * ((7 * K * lam + 2 * rho) * n) + (L + 1) < omega * n := by
  have hheavy : 128 * (21 * L * rho / lam) ≤ 21 * omega := by
    calc
      128 * (21 * L * rho / lam) = (128 * (21 * L * rho)) / lam := by ring
      _ ≤ 21 * omega := (div_le_iff₀ hlam).2 (by nlinarith [hratio])
  have hroot : 64 * (7 * K * lam + 2 * rho) ≤ 9 * omega := by
    have hkl : lam ≤ K * lam := by nlinarith
    nlinarith
  have h1 := mul_le_mul_of_nonneg_right hheavy hn.le
  have h2 := mul_le_mul_of_nonneg_right hroot hn.le
  have hop : 0 < omega * n := by nlinarith
  nlinarith

/-- A host-independent choice of c pays all three preceding numerical
conditions, including the bounded number of vertices excluded by a path. -/
theorem weighted_routing_scales (K L c lam rho omega n : ℝ)
    (hK : 1 ≤ K) (hL : 1 ≤ L) (hc : 0 < c)
    (hcsmall : 1024 * K * L * c ≤ 1)
    (homega : 0 < omega) (homega1 : omega ≤ 1)
    (hlam : 0 < lam) (hsmall : lam ≤ c * omega)
    (hrho : 0 ≤ rho) (hscale : rho ≤ c * lam ^ 2)
    (horder : 1 ≤ c * lam * n) :
    64 * K * lam ≤ omega ∧ 128 * L * rho ≤ omega * lam ∧
      rho ≤ lam ∧ 4 * (L + 1) ≤ omega * n := by
  have hK0 : 0 < K := by linarith
  have hL0 : 0 < L := by linarith
  have hcK : 1024 * K * c ≤ 1 := by nlinarith
  have hcL : 1024 * L * c ≤ 1 := by nlinarith
  have hc1 : c ≤ 1 := by nlinarith
  have hlamc : lam ≤ c := (hsmall.trans (mul_le_of_le_one_right hc.le homega1))
  have hlam1 : lam ≤ 1 := hlamc.trans hc1
  have hcl : c * lam ≤ 1 := by nlinarith
  have hrholam : rho ≤ lam := by nlinarith [hscale]
  have hn : 0 < n := by nlinarith
  have h64 : 64 * K * lam ≤ omega := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 64 * K by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hcK homega.le]
  have h128 : 128 * L * rho ≤ omega * lam := by
    have hd := routing_density_cancellation c lam rho omega hc.le hlam hscale hsmall
    have hc2 : c ^ 2 ≤ c := by nlinarith
    have hbound : 128 * L * c ^ 2 ≤ 1 := by nlinarith
    have hp := mul_le_mul_of_nonneg_left hd (show 0 ≤ 128 * L by positivity)
    have ho := mul_le_mul_of_nonneg_right hbound homega.le
    have : 128 * L * (rho / lam) ≤ omega := by nlinarith
    have hm := mul_le_mul_of_nonneg_right this hlam.le
    simpa [mul_assoc, div_mul_cancel₀ _ (ne_of_gt hlam)] using hm
  have hon : 1 ≤ c ^ 2 * (omega * n) := by
    have hh := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ c * n by positivity)
    nlinarith
  have hcL2 : 4 * (L + 1) * c ^ 2 ≤ 1 := by
    have hc2 : c ^ 2 ≤ c := by nlinarith
    nlinarith
  have hfinal : 4 * (L + 1) ≤ omega * n := by
    have hp := mul_le_mul_of_nonneg_left hon (show 0 ≤ 4 * (L + 1) by positivity)
    have hq := mul_le_mul_of_nonneg_right hcL2 (show 0 ≤ omega * n by positivity)
    nlinarith
  exact ⟨h64, h128, hrholam, hfinal⟩

#print axioms routing_density_cancellation
#print axioms weighted_routing_choice_budget
#print axioms weighted_routing_scales

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
