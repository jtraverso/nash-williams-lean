/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

@[expose] public section

/-!
# Real-number bookkeeping for the reduction of the shared refiner to an even refiner
-/

namespace PartitionedTriangleAbsorption.BlowupB.UniversalProducer

/-- The big constant fixing the small parameter `c` of the reduction. -/
noncomputable def redBig (U r m0 Tc : ℕ) (K0' : ℝ) : ℝ :=
  ((U : ℝ) + 1) * (K0' + r + 3) * (2 * m0 + 3) * (8 * m0 * Tc + 1) * (K0' + 1)

theorem one_le_redBig (U r m0 Tc : ℕ) {K0' : ℝ} (hK : 0 ≤ K0') :
    ((U : ℝ) + 1) * (K0' + r + 3) ≤ redBig U r m0 Tc K0' ∧
    (2 * m0 + 3 : ℝ) ≤ redBig U r m0 Tc K0' ∧
    (8 * m0 * Tc + 1 : ℝ) * (K0' + 1) ≤ redBig U r m0 Tc K0' ∧ 1 ≤ redBig U r m0 Tc K0' := by
  have hU : (1 : ℝ) ≤ (U : ℝ) + 1 := by have := (Nat.cast_nonneg U : (0 : ℝ) ≤ U); linarith
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
  have hT : (0 : ℝ) ≤ Tc := Nat.cast_nonneg _
  have h1 : (1 : ℝ) ≤ K0' + r + 3 := by linarith
  have h2 : (1 : ℝ) ≤ 2 * m0 + 3 := by linarith
  have h3 : (1 : ℝ) ≤ 8 * m0 * Tc + 1 := by nlinarith
  have h4 : (1 : ℝ) ≤ K0' + 1 := by linarith
  have hA : (1 : ℝ) ≤ ((U : ℝ) + 1) * (K0' + r + 3) := one_le_mul_of_one_le_of_one_le hU h1
  have hB : (1 : ℝ) ≤ (8 * m0 * Tc + 1 : ℝ) * (K0' + 1) := one_le_mul_of_one_le_of_one_le h3 h4
  have hdef : redBig U r m0 Tc K0' =
      (((U : ℝ) + 1) * (K0' + r + 3)) * (2 * m0 + 3) * ((8 * m0 * Tc + 1) * (K0' + 1)) := by
    unfold redBig; ring
  rw [hdef]
  have hA0 : (0 : ℝ) ≤ ((U : ℝ) + 1) * (K0' + r + 3) := by linarith
  have hB0 : (0 : ℝ) ≤ (8 * m0 * Tc + 1 : ℝ) * (K0' + 1) := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hAm : ((U : ℝ) + 1) * (K0' + r + 3) ≤
        ((U : ℝ) + 1) * (K0' + r + 3) * (2 * m0 + 3) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left h2 hA0
    exact hAm.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hB
        (mul_nonneg hA0 (by positivity : (0 : ℝ) ≤ 2 * m0 + 3)))
  · have hmA : (2 * m0 + 3 : ℝ) ≤
        ((U : ℝ) + 1) * (K0' + r + 3) * (2 * m0 + 3) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA
        (by positivity : (0 : ℝ) ≤ 2 * m0 + 3)
    exact hmA.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hB
        (mul_nonneg hA0 (by positivity : (0 : ℝ) ≤ 2 * m0 + 3)))
  · have h5 : (1 : ℝ) ≤ ((U : ℝ) + 1) * (K0' + r + 3) * (2 * m0 + 3) :=
      one_le_mul_of_one_le_of_one_le hA h2
    have := mul_le_mul_of_nonneg_right h5 hB0
    linarith
  · have h5 : (1 : ℝ) ≤ ((U : ℝ) + 1) * (K0' + r + 3) * (2 * m0 + 3) :=
      one_le_mul_of_one_le_of_one_le hA h2
    exact one_le_mul_of_one_le_of_one_le h5 hB

/-- **Arithmetic core of the reduction.**  With `Δ = ⌈λ n⌉ + 2 m0 + 1`, the token budget,
the token count and the degree growth all fit. -/
theorem red_arith (U r m0 Tc : ℕ) (K0' c ω lam rho n : ℝ) (hK : 0 ≤ K0')
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hcB : c ≤ 1 / (8 * redBig U r m0 Tc K0'))
    (hω : 0 < ω) (hω1 : ω ≤ 1) (hn : 0 ≤ n) (hlam : 0 < lam) (hlamc : lam ≤ c * ω)
    (hrhoc : rho ≤ c * lam ^ 2) (hcn : 1 ≤ c * lam * n) :
    ((U : ℝ) + U * ((K0' * lam * n + 2 * rho * n + r * ((⌈lam * n⌉₊ + 2 * m0 + 1 : ℕ) : ℝ)) +
        ((⌈lam * n⌉₊ + 2 * m0 + 1 : ℕ) : ℝ)) < ω * n / 2) ∧
    (4 * ((2 * m0 : ℕ) : ℝ) * (Tc * (K0' * rho * n ^ 2)) ≤
        (((⌈lam * n⌉₊ + 2 * m0 + 1 : ℕ) : ℝ) - (2 * m0 : ℕ)) * (ω * n)) ∧
    (((⌈lam * n⌉₊ + 2 * m0 + 1 : ℕ) : ℝ) ≤ 2 * (lam * n)) ∧
    (((2 * m0 : ℕ) : ℝ) < ((⌈lam * n⌉₊ + 2 * m0 + 1 : ℕ) : ℝ)) := by
  obtain ⟨hB1, hB2, hB3, hB⟩ := one_le_redBig U r m0 Tc hK
  set Bc := redBig U r m0 Tc K0' with hBc
  set x := lam * n with hx
  have hU : (0 : ℝ) ≤ U := Nat.cast_nonneg _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m0 := Nat.cast_nonneg _
  have hT : (0 : ℝ) ≤ Tc := Nat.cast_nonneg _
  have hBpos : 0 < 8 * Bc := by linarith only [hB]
  have h8 : c * (8 * Bc) ≤ 1 := by
    exact (le_div_iff₀ hBpos).mp hcB
  have hcx : 1 ≤ c * x := by rw [hx, ← mul_assoc]; exact hcn
  have hx0 : 0 ≤ x := by positivity
  have hx8 : 8 * Bc ≤ x := by
    by_contra hcon
    push_neg at hcon
    have : c * x < c * (8 * Bc) := mul_lt_mul_of_pos_left hcon hc0
    linarith only [this, hcx, h8]
  have hxω : x ≤ c * (ω * n) := by
    have := mul_le_mul_of_nonneg_right hlamc hn
    rw [hx]; linarith only [this, show c * ω * n = c * (ω * n) by ring]
  have hωn0 : 0 ≤ ω * n := by positivity
  have hωn : 8 * Bc * x ≤ ω * n := by
    have h1 : 8 * Bc * x ≤ 8 * Bc * (c * (ω * n)) := mul_le_mul_of_nonneg_left hxω hBpos.le
    have h2 : 8 * Bc * (c * (ω * n)) ≤ ω * n := by
      have := mul_le_mul_of_nonneg_right h8 hωn0
      linarith only [this, show 8 * Bc * (c * (ω * n)) = c * (8 * Bc) * (ω * n) by ring]
    exact h1.trans h2
  have hcl : c * lam ≤ 1 := by
    have hlam1 : lam ≤ 1 := hlamc.trans (by
      simpa only [one_mul] using mul_le_mul hc1 hω1 hω.le (by norm_num : (0 : ℝ) ≤ 1))
    simpa only [one_mul] using mul_le_mul hc1 hlam1 hlam.le (by norm_num : (0 : ℝ) ≤ 1)
  have hrn : rho * n ≤ c * lam * x := by
    calc rho * n ≤ (c * lam ^ 2) * n := mul_le_mul_of_nonneg_right hrhoc hn
      _ = c * lam * x := by rw [hx]; ring
  have hrx : rho * n ≤ x := hrn.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcl hx0)
  have hceil1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hDcast : ((⌈x⌉₊ + 2 * m0 + 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) + 2 * m0 + 1 := by push_cast; ring
  have hm2 : ((2 * m0 : ℕ) : ℝ) = 2 * m0 := by push_cast; ring
  rw [hDcast, hm2]
  have hm0x : 2 * (m0 : ℝ) + 3 ≤ x := by linarith only [hB2, hx8, hB]
  have hD2 : (⌈x⌉₊ : ℝ) + 2 * m0 + 1 ≤ 2 * x := by linarith only [hceil2, hm0x]
  refine ⟨?_, ?_, hD2, by linarith only [hceil1, hx0]⟩
  · have hdeg : K0' * lam * n + 2 * rho * n + r * ((⌈x⌉₊ : ℝ) + 2 * m0 + 1) +
        ((⌈x⌉₊ : ℝ) + 2 * m0 + 1) ≤ (K0' + 2 * r + 4) * x := by
      have h1 : K0' * lam * n = K0' * x := by rw [hx]; ring
      have h2 : r * ((⌈x⌉₊ : ℝ) + 2 * m0 + 1) ≤ r * (2 * x) := mul_le_mul_of_nonneg_left hD2 hr
      linarith only [h1, h2, hD2, hrx]
    have hU1 : (U : ℝ) ≤ U * x := by
      have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ x by linarith only [hx8, hB]) hU
      simpa only [mul_one] using this
    have hxpos : 0 < x := by linarith only [hx8, hB]
    have hlt : (U : ℝ) * (K0' + 2 * r + 5) < 4 * (((U : ℝ) + 1) * (K0' + r + 3)) := by
      nlinarith only [hK, hr,
        mul_nonneg hU (by linarith only [hK, hr] : (0 : ℝ) ≤ 3 * K0' + 2 * r + 7)]
    have hstep : (U : ℝ) * (K0' + 2 * r + 5) * x < 4 * Bc * x :=
      mul_lt_mul_of_pos_right (hlt.trans_le (by linarith only [hB1])) hxpos
    have h3 := mul_le_mul_of_nonneg_left hdeg hU
    have h4 : (U : ℝ) * ((K0' + 2 * r + 4) * x) + U * x = U * (K0' + 2 * r + 5) * x := by ring
    linarith only [h3, h4, hU1, hstep, hωn]
  · have hrn2 : rho * n ^ 2 ≤ c * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hrn hn
      have h2 : c * lam * x * n = c * x ^ 2 := by rw [hx]; ring
      calc rho * n ^ 2 = rho * n * n := by ring
        _ ≤ c * lam * x * n := this
        _ = c * x ^ 2 := h2
    have hx2 : x ^ 2 ≤ c * x * (ω * n) := by
      have := mul_le_mul_of_nonneg_left hxω hx0
      calc x ^ 2 = x * x := by ring
        _ ≤ x * (c * (ω * n)) := this
        _ = c * x * (ω * n) := by ring
    have hconst : 8 * m0 * Tc * K0' * c ≤ 1 / 8 := by
      have h1 : 8 * m0 * Tc * K0' ≤ Bc := by
        have e : (8 * (m0 : ℝ) * Tc + 1) * (K0' + 1) = 8 * m0 * Tc * K0' + 8 * m0 * Tc + K0' + 1 := by
          ring
        have : (0 : ℝ) ≤ 8 * m0 * Tc := by positivity
        linarith only [e, this, hK, hB3]
      have := mul_le_mul_of_nonneg_right h1 hc0.le
      linarith only [this, h8]
    have hLHS : 4 * (2 * (m0 : ℝ)) * (Tc * (K0' * rho * n ^ 2)) =
        (8 * m0 * Tc * K0') * (rho * n ^ 2) := by ring
    have hk0 : 0 ≤ 8 * m0 * Tc * K0' := by positivity
    have h1 : (8 * m0 * Tc * K0') * (rho * n ^ 2) ≤ (8 * m0 * Tc * K0') * (c * x ^ 2) :=
      mul_le_mul_of_nonneg_left hrn2 hk0
    have h2 : (8 * m0 * Tc * K0') * (c * x ^ 2) ≤ (8 * m0 * Tc * K0') * (c * (c * x * (ω * n))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx2 hc0.le) hk0
    have h3 : (8 * m0 * Tc * K0') * (c * (c * x * (ω * n))) =
        (8 * m0 * Tc * K0' * c) * c * (x * (ω * n)) := by ring
    have hxw : 0 ≤ x * (ω * n) := mul_nonneg hx0 hωn0
    have h4 : (8 * m0 * Tc * K0' * c) * c * (x * (ω * n)) ≤ x * (ω * n) := by
      have hk1 : 0 ≤ 8 * m0 * Tc * K0' * c := mul_nonneg hk0 hc0.le
      have : (8 * m0 * Tc * K0' * c) * c ≤ 1 / 8 * 1 := mul_le_mul hconst hc1 hc0.le (by norm_num)
      exact mul_le_of_le_one_left hxw (by linarith only [this])
    have h5 : x * (ω * n) ≤ ((⌈x⌉₊ : ℝ) + 2 * m0 + 1 - 2 * m0) * (ω * n) :=
      mul_le_mul_of_nonneg_right (by linarith only [hceil1]) hωn0
    linarith only [hLHS, h1, h2, h3, h4, h5]

end PartitionedTriangleAbsorption.BlowupB.UniversalProducer
