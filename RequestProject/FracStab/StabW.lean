/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import RequestProject.FracStab.StabAlg

@[expose] public section

/-!
# Stability consequences for nearly matched four part configurations

Here `xi, xj, xk, xl` are the four part sizes (summing to `1`) and `mij, …` the six pair
weights of a triangle-thin `[0,1]`-weighted `K₄` whose four triangle sums are all within `s` of
`2` (this is what `regimeB_big` provides).  Two consequences are recorded:

* `smallpair_cut`: if one pair weight is small, the configuration is close to a *cut*;
* `matching_balance`: if the weight of the matching `{ij, kl}` is bounded away from `1`, then the
  bipartition `{i,j} | {k,l}` is almost balanced.
-/

namespace NashWilliams.Frac

/-- Linear programming inequality behind `matching_balance`. -/
lemma lp_three {p1 p2 p3 P1 P2 P3 : ℝ} (h2 : p2 ≤ 1) (h3 : p3 ≤ 1) (hs : p1 + p2 + p3 ≤ 2)
    (hP2 : 0 ≤ P2) (hP3 : 0 ≤ P3) (h12 : P1 + P2 ≤ 1/4) (h13 : P1 + P3 ≤ 1/4) (hp1 : 0 ≤ p1) :
    p1*P1 + p2*P2 + p3*P3 ≤ (1-p1)*(P2+P3) + p1/4 := by
  rcases le_total P2 P3 with h | h
  · nlinarith [mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 - p1 - p2 - p3) hP2,
      mul_nonneg hp1 (by linarith : (0:ℝ) ≤ 1/4 - P1 - P3)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h),
      mul_nonneg (by linarith : (0:ℝ) ≤ 2 - p1 - p2 - p3) hP3,
      mul_nonneg hp1 (by linarith : (0:ℝ) ≤ 1/4 - P1 - P2)]

/-- `4 x y ≤ (x + y)^2`. -/
lemma four_mul_le_sq (x y : ℝ) : 4 * (x * y) ≤ (x + y) ^ 2 := by nlinarith [sq_nonneg (x - y)]

lemma mul_le_quarter {y y' : ℝ} (hy : 0 ≤ y) (hy' : 0 ≤ y') (h : y + y' ≤ 1) :
    y * y' ≤ 1/4 := by
  nlinarith [four_mul_le_sq y y']

/-- Hypotheses shared by the two lemmas below. -/
structure NearMatched (xi xj xk xl mij mik mil mjk mjl mkl s : ℝ) : Prop where
  xi0 : 0 ≤ xi
  xj0 : 0 ≤ xj
  xk0 : 0 ≤ xk
  xl0 : 0 ≤ xl
  sum : xi + xj + xk + xl = 1
  thin : ThinK4 mij mik mil mjk mjl mkl
  sijk : 2 - mij - mik - mjk ≤ s
  sijl : 2 - mij - mil - mjl ≤ s
  sikl : 2 - mik - mil - mkl ≤ s
  sjkl : 2 - mjk - mjl - mkl ≤ s

/-- The value of the configuration. -/
def val4 (xi xj xk xl mij mik mil mjk mjl mkl : ℝ) : ℝ :=
  mij*xi*xj + mik*xi*xk + mil*xi*xl + mjk*xj*xk + mjl*xj*xl + mkl*xk*xl

lemma NearMatched.match_err {xi xj xk xl mij mik mil mjk mjl mkl s : ℝ}
    (H : NearMatched xi xj xk xl mij mik mil mjk mjl mkl s) :
    |mij - mkl| ≤ s ∧ |mik - mjl| ≤ s ∧ |mil - mjk| ≤ s := by
  obtain ⟨-, -, -, -, -, hT, h1, h2, h3, h4⟩ := H
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, t1, t2, t3, t4⟩ := hT
  refine ⟨abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩, abs_le.2 ⟨?_, ?_⟩⟩ <;> linarith

/-- **A small pair weight forces a cut.**  If `mij ≤ τ`, then all four pairs across the
bipartition `{i,j} | {k,l}` have weight at least `1 - s - τ`, and the bipartition is almost
balanced. -/
lemma smallpair_cut {xi xj xk xl mij mik mil mjk mjl mkl s τ D : ℝ}
    (H : NearMatched xi xj xk xl mij mik mil mjk mjl mkl s)
    (hval : 1/4 - D ≤ val4 xi xj xk xl mij mik mil mjk mjl mkl) (hsmall : mij ≤ τ) :
    1 - mik ≤ s + τ ∧ 1 - mil ≤ s + τ ∧ 1 - mjk ≤ s + τ ∧ 1 - mjl ≤ s + τ ∧
      (xi + xj - 1/2)^2 ≤ D + τ/2 + s/4 := by
  have hm := H.match_err
  obtain ⟨hi, hj, hk, hl, hsum, hT, h1, h2, h3, h4⟩ := H
  obtain ⟨n12, n13, n14, n23, n24, n34, l12, l13, l14, l23, l24, l34, t1, t2, t3, t4⟩ := hT
  have hkl : mkl ≤ τ + s := by linarith only [(abs_le.1 hm.1).1, hsmall]
  refine ⟨by linarith only [h1, l23, hsmall], by linarith only [h2, l24, hsmall],
    by linarith only [h1, l13, hsmall], by linarith only [h2, l14, hsmall], ?_⟩
  have q1 : mij * xi * xj ≤ τ * (1/4) := by
    have : xi * xj ≤ 1/4 := mul_le_quarter hi hj (by linarith only [hsum, hk, hl])
    calc mij * xi * xj = mij * (xi * xj) := by ring
      _ ≤ τ * (xi * xj) := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hi hj)
      _ ≤ τ * (1/4) := mul_le_mul_of_nonneg_left this (le_trans n12 hsmall)
  have q2 : mkl * xk * xl ≤ (τ + s) * (1/4) := by
    have : xk * xl ≤ 1/4 := mul_le_quarter hk hl (by linarith only [hsum, hi, hj])
    calc mkl * xk * xl = mkl * (xk * xl) := by ring
      _ ≤ (τ + s) * (xk * xl) := mul_le_mul_of_nonneg_right hkl (mul_nonneg hk hl)
      _ ≤ (τ + s) * (1/4) := mul_le_mul_of_nonneg_left this (le_trans n34 hkl)
  have c : ∀ {m y : ℝ}, m ≤ 1 → 0 ≤ y → m * y ≤ y := fun hm hy => by
    simpa using mul_le_mul_of_nonneg_right hm hy
  have c1 : mik * xi * xk ≤ xi * xk := by rw [mul_assoc]; exact c l13 (mul_nonneg hi hk)
  have c2 : mil * xi * xl ≤ xi * xl := by rw [mul_assoc]; exact c l14 (mul_nonneg hi hl)
  have c3 : mjk * xj * xk ≤ xj * xk := by rw [mul_assoc]; exact c l23 (mul_nonneg hj hk)
  have c4 : mjl * xj * xl ≤ xj * xl := by rw [mul_assoc]; exact c l24 (mul_nonneg hj hl)
  unfold val4 at hval
  have hxkl : xk + xl = 1 - (xi + xj) := by linarith only [hsum]
  have e : (xi + xj - 1/2)^2 = 1/4 - (xi * xk + xi * xl + xj * xk + xj * xl) := by
    have : xi * xk + xi * xl + xj * xk + xj * xl = (xi + xj) * (xk + xl) := by ring
    rw [this, hxkl]; ring
  rw [e]
  linarith only [hval, q1, q2, c1, c2, c3, c4]

/-- **Balance of the bipartition of a heavy-deficient matching.**  If the weight of `ij` is at
most `1 - τ` (with `2 s ≤ τ`), then `{i,j} | {k,l}` is almost balanced. -/
lemma matching_balance {xi xj xk xl mij mik mil mjk mjl mkl s τ D : ℝ}
    (H : NearMatched xi xj xk xl mij mik mil mjk mjl mkl s)
    (hval : 1/4 - D ≤ val4 xi xj xk xl mij mik mil mjk mjl mkl) (hm : mij ≤ 1 - τ)
    (hsτ : 2 * s ≤ τ) :
    (xi + xj - 1/2)^2 * τ ≤ 2 * D + 2 * s := by
  have hme := H.match_err
  obtain ⟨hi, hj, hk, hl, hsum, hT, h1, h2, h3, h4⟩ := H
  obtain ⟨n12, n13, n14, n23, n24, n34, l12, l13, l14, l23, l24, l34, t1, t2, t3, t4⟩ := hT
  set P1 := xi*xj + xk*xl
  set P2 := xi*xk + xj*xl
  set P3 := xi*xl + xj*xk
  set p1 := (mij + mkl)/2
  set p2 := (mik + mjl)/2
  set p3 := (mil + mjk)/2
  have hP1 : 0 ≤ P1 := by positivity
  have hP2 : 0 ≤ P2 := by positivity
  have hP3 : 0 ≤ P3 := by positivity
  have hA : P1 + P2 ≤ 1/4 := by
    have := four_mul_le_sq (xi + xl) (xj + xk)
    have e : P1 + P2 = (xi + xl) * (xj + xk) := by simp only [P1, P2]; ring
    rw [e]; nlinarith
  have hB : P1 + P3 ≤ 1/4 := by
    have := four_mul_le_sq (xi + xk) (xj + xl)
    have e : P1 + P3 = (xi + xk) * (xj + xl) := by simp only [P1, P3]; ring
    rw [e]; nlinarith
  have hlp := lp_three (p1 := p1) (p2 := p2) (p3 := p3) (by simp only [p2]; linarith)
    (by simp only [p3]; linarith) (by simp only [p1, p2, p3]; linarith) hP2 hP3 hA hB
    (by simp only [p1]; linarith)
  -- the value differs from `p1 P1 + p2 P2 + p3 P3` by at most `3 s / 8`
  have err : ∀ {m m' y y' : ℝ}, |m - m'| ≤ s → 0 ≤ y → 0 ≤ y' → y ≤ 1/4 → y' ≤ 1/4 →
      m * y + m' * y' ≤ (m + m') / 2 * (y + y') + s / 8 := by
    intro m m' y y' hmm hy hy' hy4 hy4'
    have e : m * y + m' * y' = (m + m') / 2 * (y + y') + (m - m') * (y - y') / 2 := by ring
    have h1 : |y - y'| ≤ 1/4 := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : (m - m') * (y - y') ≤ s * (1/4) := by
      calc (m - m') * (y - y') ≤ |(m - m') * (y - y')| := le_abs_self _
        _ = |m - m'| * |y - y'| := abs_mul _ _
        _ ≤ s * (1/4) := mul_le_mul hmm h1 (abs_nonneg _) (le_trans (abs_nonneg _) hmm)
    linarith
  have q : ∀ {y y' : ℝ}, 0 ≤ y → 0 ≤ y' → y + y' ≤ 1 → y * y' ≤ 1/4 :=
    fun hy hy' h => mul_le_quarter hy hy' h
  have e1 := err hme.1 (mul_nonneg hi hj) (mul_nonneg hk hl) (q hi hj (by linarith))
    (q hk hl (by linarith))
  have e2 := err hme.2.1 (mul_nonneg hi hk) (mul_nonneg hj hl) (q hi hk (by linarith))
    (q hj hl (by linarith))
  have e3 := err hme.2.2 (mul_nonneg hi hl) (mul_nonneg hj hk) (q hi hl (by linarith))
    (q hj hk (by linarith))
  have hv : val4 xi xj xk xl mij mik mil mjk mjl mkl ≤ p1*P1 + p2*P2 + p3*P3 + 3 * s / 8 := by
    unfold val4
    have : mij*xi*xj + mik*xi*xk + mil*xi*xl + mjk*xj*xk + mjl*xj*xl + mkl*xk*xl =
        (mij * (xi*xj) + mkl * (xk*xl)) + (mik * (xi*xk) + mjl * (xj*xl)) +
          (mil * (xi*xl) + mjk * (xj*xk)) := by ring
    rw [this]; simp only [p1, p2, p3, P1, P2, P3]; linarith
  have hC : (xi + xj - 1/2)^2 = 1/4 - (P2 + P3) := by
    have hxkl : xk + xl = 1 - (xi + xj) := by linarith
    have e : P2 + P3 = (xi + xj) * (xk + xl) := by simp only [P2, P3]; ring
    rw [e, hxkl]; ring
  have hp1 : p1 ≤ 1 - τ + s / 2 := by simp only [p1]; linarith [(abs_le.1 hme.1).1]
  have key : (1 - p1) * (xi + xj - 1/2)^2 ≤ D + 3 * s / 8 := by
    rw [hC]
    have e : (1-p1)*(1/4-(P2+P3)) = (1-p1)/4 - (1-p1)*(P2+P3) := by ring
    rw [e]; linarith only [hval, hv, hlp]
  have hsq : 0 ≤ (xi + xj - 1/2)^2 := sq_nonneg _
  have hs0 : 0 ≤ s := by linarith only [h1, t1]
  have h5 := mul_le_mul_of_nonneg_right (by linarith only [hp1, hsτ, hs0] : τ / 2 ≤ 1 - p1) hsq
  have e : (xi + xj - 1/2)^2 * τ = 2 * (τ / 2 * (xi + xj - 1/2)^2) := by ring
  rw [e]; linarith only [h5, key, hs0]

end NashWilliams.Frac
