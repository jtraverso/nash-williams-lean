/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1TemplateRightInverseStage233

/-!
# Linearity and the uniform bound of the F1 template right inverse

* every building block of `Rv` is linear in the edge vector, so `Rv` is a linear map `Rlin`;
* if `|x f| ≤ ε` for all `f`, then `|Rv x e| ≤ 20 ε / t` for every pair `e` (`t ≥ 4`).
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1TemplateStage233

open Finset TypedApplicationLinks F1GramInverseStage230

variable {t : ℕ}

/-! ### Linearity -/

section Linear

variable (x y : Sym2 (Fin 4 × Fin t) → ℝ) (α β : ℝ)

theorem rI_lin (i : Fin 4) (a : Fin t) :
    rI (α • x + β • y) i a = α * rI x i a + β * rI y i a := by
  simp only [rI, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem rC_lin (i : Fin 4) (a : Fin t) (j : Fin 4) :
    rC (α • x + β • y) i a j = α * rC x i a j + β * rC y i a j := by
  simp only [rC, mul_sum, ← sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem mI_lin (i : Fin 4) : mI (α • x + β • y) i = α * mI x i + β * mI y i := by
  simp only [mI, rI_lin, sum_add_distrib, ← mul_sum]; ring

theorem mC_lin (i j : Fin 4) : mC (α • x + β • y) i j = α * mC x i j + β * mC y i j := by
  simp only [mC, rC_lin, sum_add_distrib, ← mul_sum]; ring

theorem aC_lin (i : Fin 4) (a : Fin t) :
    aC (α • x + β • y) i a = α * aC x i a + β * aC y i a := by
  simp only [aC, rI_lin, mI_lin]; ring

theorem bC_lin (i : Fin 4) (a : Fin t) (j : Fin 4) :
    bC (α • x + β • y) i a j = α * bC x i a j + β * bC y i a j := by
  simp only [bC, rC_lin, mC_lin]; ring

theorem cI_lin (i : Fin 4) : cI (α • x + β • y) i = α * cI x i + β * cI y i := by
  fin_cases i <;> simp [cI, intCoef, blockInverse, blocksOf, mI_lin, mC_lin] <;> ring

theorem cC_lin (i j : Fin 4) : cC (α • x + β • y) i j = α * cC x i j + β * cC y i j := by
  fin_cases i <;> fin_cases j <;>
    simp [cC, crossCoef, blockInverse, blocksOf, mI_lin, mC_lin] <;> ring

theorem Pc_lin (i : Fin 4) (a : Fin t) :
    Pc (α • x + β • y) i a = α * Pc x i a + β * Pc y i a := by
  simp only [Pc, starInternal, aC_lin, bC_lin]; ring

theorem Qc_lin (i : Fin 4) (a : Fin t) (j : Fin 4) :
    Qc (α • x + β • y) i a j = α * Qc x i a j + β * Qc y i a j := by
  simp only [Qc, bC_lin, Pc_lin]; ring

theorem zI_lin (i : Fin 4) (a b : Fin t) :
    zI (α • x + β • y) i a b = α * zI x i a b + β * zI y i a b := by
  simp only [zI, mI_lin, aC_lin, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem zC_lin (i : Fin 4) (a : Fin t) (j : Fin 4) (b : Fin t) :
    zC (α • x + β • y) i a j b = α * zC x i a j b + β * zC y i a j b := by
  simp only [zC, mC_lin, bC_lin, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem Rv_lin (e : Sym2 (Fin 4 × Fin t)) :
    Rv (α • x + β • y) e = α * Rv x e + β * Rv y e := by
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Rv_mk, Rf]
    split_ifs
    · ring
    · simp only [cI_lin, Pc_lin, zI_lin]; ring
    · simp only [cC_lin, Qc_lin, zC_lin]; ring
    · ring

end Linear

/-- The right inverse as a linear map. -/
noncomputable def Rlin (t : ℕ) : (Sym2 (Fin 4 × Fin t) → ℝ) →ₗ[ℝ] (Sym2 (Fin 4 × Fin t) → ℝ) where
  toFun := Rv
  map_add' x y := by
    funext e
    have := Rv_lin x y 1 1 e
    simpa using this
  map_smul' c x := by
    funext e
    have := Rv_lin x 0 c 0 e
    simpa using this

theorem Rlin_apply (x : Sym2 (Fin 4 × Fin t) → ℝ) : Rlin t x = Rv x := rfl

/-! ### Uniform bounds -/

section Bounds

variable (x : Sym2 (Fin 4 × Fin t) → ℝ) {ε : ℝ} (hε : 0 ≤ ε) (hx : ∀ e, |x e| ≤ ε)
include hε hx

omit hε in
theorem abs_rI (i : Fin 4) (a : Fin t) : |rI x i a| ≤ (t - 1) * ε := by
  unfold rI
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ b, |(if b = a then 0 else x s((i, a), (i, b)))| ≤ if b = a then 0 else ε := by
    intro b; split_ifs
    · simp
    · exact hx _
  refine (sum_le_sum fun b _ => this b).trans (le_of_eq ?_)
  rw [sum_ne_index (fun _ => ε)]
  simp; ring

omit hε in
theorem abs_rC (i : Fin 4) (a : Fin t) (j : Fin 4) : |rC x i a j| ≤ t * ε := by
  unfold rC
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun b _ => hx _).trans (le_of_eq ?_)
  simp

variable (ht : 4 ≤ t)
include ht

omit hε in
theorem abs_mI (i : Fin 4) : |mI x i| ≤ ε := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hpos : (0 : ℝ) < t * (t - 1) := by nlinarith
  unfold mI
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun a _ => abs_rI x hx i a).trans (le_of_eq ?_)
  simp; ring

omit hε in
theorem abs_mC (i j : Fin 4) : |mC x i j| ≤ ε := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hpos : (0 : ℝ) < t * t := by nlinarith
  unfold mC
  rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  refine (sum_le_sum fun a _ => abs_rC x hx i a j).trans (le_of_eq ?_)
  simp; ring

theorem abs_aC (i : Fin 4) (a : Fin t) : |aC x i a| ≤ 3 * ε := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h2 : (0 : ℝ) < t - 2 := by linarith
  unfold aC
  rw [abs_div, abs_of_pos h2, div_le_iff₀ h2]
  have h1 := abs_rI x hx i a
  have h3 := abs_mI x hx ht i
  calc |rI x i a - (t - 1) * mI x i| ≤ |rI x i a| + |(t - 1) * mI x i| := abs_sub _ _
    _ = |rI x i a| + (t - 1) * |mI x i| := by
        rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < t - 1)]
    _ ≤ (t - 1) * ε + (t - 1) * ε := by gcongr; linarith
    _ ≤ 3 * ε * (t - 2) := by nlinarith

omit hε in
theorem abs_bC (i : Fin 4) (a : Fin t) (j : Fin 4) : |bC x i a j| ≤ 2 * ε := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (0 : ℝ) < t := by linarith
  unfold bC
  have h1 : |rC x i a j / t| ≤ ε := by
    rw [abs_div, abs_of_pos h0, div_le_iff₀ h0]; linarith [abs_rC x hx i a j]
  have h3 := abs_mC x hx ht i j
  calc |rC x i a j / t - mC x i j| ≤ |rC x i a j / t| + |mC x i j| := abs_sub _ _
    _ ≤ 2 * ε := by linarith

theorem abs_zI (i : Fin 4) (a b : Fin t) : |zI x i a b| ≤ 8 * ε := by
  unfold zI
  have := hx s((i, a), (i, b))
  have := abs_mI x hx ht i
  have := abs_aC x hε hx ht i a
  have := abs_aC x hε hx ht i b
  calc _ ≤ |x s((i, a), (i, b)) - mI x i - aC x i a| + |aC x i b| := abs_sub _ _
    _ ≤ |x s((i, a), (i, b)) - mI x i| + |aC x i a| + |aC x i b| := by
        gcongr; exact abs_sub _ _
    _ ≤ |x s((i, a), (i, b))| + |mI x i| + |aC x i a| + |aC x i b| := by
        gcongr; exact abs_sub _ _
    _ ≤ 8 * ε := by linarith

omit hε in
theorem abs_zC (i : Fin 4) (a : Fin t) (j : Fin 4) (b : Fin t) : |zC x i a j b| ≤ 6 * ε := by
  unfold zC
  have := hx s((i, a), (j, b))
  have := abs_mC x hx ht i j
  have := abs_bC x hx ht i a j
  have := abs_bC x hx ht j b i
  calc _ ≤ |x s((i, a), (j, b)) - mC x i j - bC x i a j| + |bC x j b i| := abs_sub _ _
    _ ≤ |x s((i, a), (j, b)) - mC x i j| + |bC x i a j| + |bC x j b i| := by
        gcongr; exact abs_sub _ _
    _ ≤ |x s((i, a), (j, b))| + |mC x i j| + |bC x i a j| + |bC x j b i| := by
        gcongr; exact abs_sub _ _
    _ ≤ 6 * ε := by linarith

theorem blocks_bound :
    |(blockInverse (blocksOf x)).i0| ≤ 5 * (ε / t) ∧ |(blockInverse (blocksOf x)).i1| ≤ 5 * (ε / t) ∧
    |(blockInverse (blocksOf x)).i2| ≤ 5 * (ε / t) ∧ |(blockInverse (blocksOf x)).i3| ≤ 5 * (ε / t) ∧
    |(blockInverse (blocksOf x)).c02| ≤ 3 * (ε / t) ∧
    |(blockInverse (blocksOf x)).c03| ≤ 3 * (ε / t) ∧
    |(blockInverse (blocksOf x)).c12| ≤ 3 * (ε / t) ∧
    |(blockInverse (blocksOf x)).c13| ≤ 3 * (ε / t) := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (0 : ℝ) < t := by linarith
  have h1 : (0 : ℝ) < t - 1 := by linarith
  have hI : ∀ i, |mI x i / (2 * t)| ≤ ε / t / 2 := by
    intro i
    rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * t)]
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * t)]
    have := abs_mI x hx ht i
    have : ε / t / 2 * (2 * t) = ε := by field_simp
    linarith
  have hC : ∀ i j, |mC x i j / (t - 1)| ≤ 2 * (ε / t) := by
    intro i j
    rw [abs_div, abs_of_pos h1, div_le_iff₀ h1]
    have := abs_mC x hx ht i j
    have : 2 * (ε / t) * (t - 1) = ε + ε * (t - 2) / t := by field_simp; ring
    have : 0 ≤ ε * (t - 2) / t := by
      apply div_nonneg _ h0.le; nlinarith
    linarith
  exact blockInverse_bound (blocksOf x) (ε / t) (div_nonneg hε h0.le)
    (hI 0) (hI 1) (hI 2) (hI 3) (hC 0 2) (hC 0 3) (hC 1 2) (hC 1 3)

theorem abs_cI (i : Fin 4) : |cI x i| ≤ 5 * (ε / t) := by
  obtain ⟨h0, h1, h2, h3, -⟩ := blocks_bound x hε hx ht
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem abs_cC (i j : Fin 4) : |cC x i j| ≤ 3 * (ε / t) := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hr : 0 ≤ 3 * (ε / t) := by positivity
  obtain ⟨-, -, -, -, h02, h03, h12, h13⟩ := blocks_bound x hε hx ht
  fin_cases i <;> fin_cases j <;> simp [cC, crossCoef] <;> first | assumption | positivity

theorem abs_Pc (i : Fin 4) (a : Fin t) : |Pc x i a| ≤ 5 * ε / t := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  exact starInternal_bound t _ _ _ ε ht' hε (abs_aC x hε hx ht i a) (abs_bC x hx ht i a _)
    (abs_bC x hx ht i a _)

theorem abs_Qc (i : Fin 4) (a : Fin t) (j : Fin 4) (h : Opp i j) : |Qc x i a j| ≤ 4 * ε / t := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have hj : j = first1 i ∨ j = second1 i := by
    fin_cases i <;> fin_cases j <;> simp [Opp] at h <;> simp [first1, second1]
  rcases hj with rfl | rfl
  · exact starCross_bound t _ _ _ ε ht' hε (abs_aC x hε hx ht i a) (abs_bC x hx ht i a _)
      (abs_bC x hx ht i a _)
  · have hs : starInternal t (aC x i a) (bC x i a (second1 i)) (bC x i a (first1 i)) =
        starInternal t (aC x i a) (bC x i a (first1 i)) (bC x i a (second1 i)) := by
      simp only [starInternal, add_comm (bC x i a (second1 i))]
    have e2 : Qc x i a (second1 i) =
        starCross t (aC x i a) (bC x i a (second1 i)) (bC x i a (first1 i)) := by
      simp only [Qc, starCross, hs, Pc]
    rw [e2]
    exact starCross_bound t _ _ _ ε ht' hε (abs_aC x hε hx ht i a) (abs_bC x hx ht i a _)
      (abs_bC x hx ht i a _)

/-- **Uniform bound of the right inverse**: `‖R x‖∞ ≤ 20 ‖x‖∞ / t`. -/
theorem abs_Rv (e : Sym2 (Fin 4 × Fin t)) : |Rv x e| ≤ 20 * ε / t := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (0 : ℝ) < t := by linarith
  have hεt : 0 ≤ ε / t := div_nonneg hε h0.le
  induction e using Sym2.ind with
  | _ u v =>
    simp only [Rv_mk, Rf]
    split_ifs with h1 h2 h3
    · simp; positivity
    · have a1 := abs_cI x hε hx ht u.1
      have a2 := abs_Pc x hε hx ht u.1 u.2
      have a3 := abs_Pc x hε hx ht u.1 v.2
      have a4 : |zI x u.1 u.2 v.2 / (2 * t)| ≤ 4 * (ε / t) := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * t),
          div_le_iff₀ (by linarith : (0 : ℝ) < 2 * t)]
        have := abs_zI x hε hx ht u.1 u.2 v.2
        have : 4 * (ε / t) * (2 * t) = 8 * ε := by field_simp; ring
        linarith
      have e1 : 5 * ε / t = 5 * (ε / t) := by ring
      have e2 : 20 * ε / t = 20 * (ε / t) := by ring
      rw [e1] at a2 a3
      rw [e2]
      calc _ ≤ |cI x u.1 + Pc x u.1 u.2 + Pc x u.1 v.2| + |zI x u.1 u.2 v.2 / (2 * t)| :=
            abs_add_le _ _
        _ ≤ |cI x u.1 + Pc x u.1 u.2| + |Pc x u.1 v.2| + |zI x u.1 u.2 v.2 / (2 * t)| := by
            gcongr; exact abs_add_le _ _
        _ ≤ |cI x u.1| + |Pc x u.1 u.2| + |Pc x u.1 v.2| + |zI x u.1 u.2 v.2 / (2 * t)| := by
            gcongr; exact abs_add_le _ _
        _ ≤ 20 * (ε / t) := by linarith
    · have a1 := abs_cC x hε hx ht u.1 v.1
      have a2 := abs_Qc x hε hx ht u.1 u.2 v.1 h3
      have a3 := abs_Qc x hε hx ht v.1 v.2 u.1 (opp_symm h3)
      have a4 : |zC x u.1 u.2 v.1 v.2 / (2 * t - 4)| ≤ 6 * (ε / t) := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 2 * t - 4),
          div_le_iff₀ (by linarith : (0 : ℝ) < 2 * t - 4)]
        have := abs_zC x hx ht u.1 u.2 v.1 v.2
        have : 6 * (ε / t) * (2 * t - 4) = 6 * ε + 6 * ε * (t - 4) / t := by
          field_simp; ring
        have : 0 ≤ 6 * ε * (t - 4) / t := by
          apply div_nonneg _ h0.le; nlinarith
        linarith
      have e1 : 4 * ε / t = 4 * (ε / t) := by ring
      have e2 : 20 * ε / t = 20 * (ε / t) := by ring
      rw [e1] at a2 a3
      rw [e2]
      calc _ ≤ |cC x u.1 v.1 + Qc x u.1 u.2 v.1 + Qc x v.1 v.2 u.1| +
            |zC x u.1 u.2 v.1 v.2 / (2 * t - 4)| := abs_add_le _ _
        _ ≤ |cC x u.1 v.1 + Qc x u.1 u.2 v.1| + |Qc x v.1 v.2 u.1| +
            |zC x u.1 u.2 v.1 v.2 / (2 * t - 4)| := by gcongr; exact abs_add_le _ _
        _ ≤ |cC x u.1 v.1| + |Qc x u.1 u.2 v.1| + |Qc x v.1 v.2 u.1| +
            |zC x u.1 u.2 v.1 v.2 / (2 * t - 4)| := by gcongr; exact abs_add_le _ _
        _ ≤ 20 * (ε / t) := by linarith
    · simp; positivity

end Bounds

end PartitionedTriangleAbsorption.F1TemplateStage233
