/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.F1TemplateIncidenceStage233
public import PartitionedTriangleAbsorption.F1GramInverseStage230

/-!
# The explicit right inverse of the F1 template Gram operator

For an edge vector `x` of the complete F1 template on `Fin 4 × Fin t` we split `x` into block
means, vertex contrasts and zero-row remainders, and invert each part with the scalar formulas of
`F1GramInverseStage230`. The resulting vector `R x` satisfies `gram (R x) = x` on every allowed
pair when the block means are balanced (`(blocksOf x).Balanced`), and `|R x e| ≤ 19 ε / t`
whenever `|x f| ≤ ε` for all `f`.
-/

@[expose] public section

namespace PartitionedTriangleAbsorption.F1TemplateStage233

open Finset TypedApplicationLinks F1GramInverseStage230

variable {t : ℕ}

/-! ### Block data of an edge vector -/

/-- Internal row sum at `(i,a)` (diagonal excluded). -/
def rI (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) : ℝ :=
  ∑ b, if b = a then 0 else x s((i, a), (i, b))

/-- Row sum at `(i,a)` into class `j`. -/
def rC (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) (j : Fin 4) : ℝ :=
  ∑ b, x s((i, a), (j, b))

/-- Mean over the internal block `i`. -/
noncomputable def mI (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) : ℝ :=
  (∑ a, rI x i a) / (t * (t - 1))

/-- Mean over the cross block `ij`. -/
noncomputable def mC (x : Sym2 (Fin 4 × Fin t) → ℝ) (i j : Fin 4) : ℝ :=
  (∑ a, rC x i a j) / (t * t)

/-- Internal vertex contrast. -/
noncomputable def aC (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) : ℝ :=
  (rI x i a - (t - 1) * mI x i) / (t - 2)

/-- Cross vertex contrast. -/
noncomputable def bC (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) (j : Fin 4) : ℝ :=
  rC x i a j / t - mC x i j

/-- Internal coefficients of a `Blocks` vector, indexed by class. -/
def intCoef (y : Blocks) : Fin 4 → ℝ := ![y.i0, y.i1, y.i2, y.i3]

/-- Cross coefficients of a `Blocks` vector, as a symmetric table. -/
def crossCoef (y : Blocks) : Fin 4 → Fin 4 → ℝ :=
  ![![0, 0, y.c02, y.c03], ![0, 0, y.c12, y.c13], ![y.c02, y.c12, 0, 0], ![y.c03, y.c13, 0, 0]]

theorem crossCoef_symm (y : Blocks) (i j : Fin 4) : crossCoef y i j = crossCoef y j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem blockMap_int (y : Blocks) (i : Fin 4) :
    intCoef (blockMap y) i =
      intCoef y i + crossCoef y i (first1 i) + crossCoef y i (second1 i) := by
  fin_cases i <;> simp [intCoef, crossCoef, blockMap, first1, second1]

theorem blockMap_cross (y : Blocks) (i j : Fin 4) (h : Opp i j) :
    crossCoef (blockMap y) i j = intCoef y i + intCoef y j + 4 * crossCoef y i j := by
  fin_cases i <;> fin_cases j <;> simp [Opp] at h <;>
    simp [intCoef, crossCoef, blockMap] <;> ring

/-- The normalized block means of `x`. -/
noncomputable def blocksOf (x : Sym2 (Fin 4 × Fin t) → ℝ) : Blocks :=
  ⟨mI x 0 / (2 * t), mI x 1 / (2 * t), mI x 2 / (2 * t), mI x 3 / (2 * t),
    mC x 0 2 / (t - 1), mC x 0 3 / (t - 1), mC x 1 2 / (t - 1), mC x 1 3 / (t - 1)⟩

/-- Constant coefficient on internal block `i`. -/
noncomputable def cI (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) : ℝ :=
  intCoef (blockInverse (blocksOf x)) i

/-- Constant coefficient on cross block `ij`. -/
noncomputable def cC (x : Sym2 (Fin 4 × Fin t) → ℝ) (i j : Fin 4) : ℝ :=
  crossCoef (blockInverse (blocksOf x)) i j

/-- Internal star coefficient of the vertex `(i,a)`. -/
noncomputable def Pc (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) : ℝ :=
  starInternal t (aC x i a) (bC x i a (first1 i)) (bC x i a (second1 i))

/-- Cross star coefficient of the vertex `(i,a)` towards class `j`. -/
noncomputable def Qc (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) (j : Fin 4) : ℝ :=
  (bC x i a j - (t - 2) * Pc x i a) / (3 * t - 4)

/-- Internal remainder. -/
noncomputable def zI (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a b : Fin t) : ℝ :=
  x s((i, a), (i, b)) - mI x i - aC x i a - aC x i b

/-- Cross remainder. -/
noncomputable def zC (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) (j : Fin 4)
    (b : Fin t) : ℝ :=
  x s((i, a), (j, b)) - mC x i j - bC x i a j - bC x j b i

/-- The right inverse on ordered pairs. -/
noncomputable def Rf (x : Sym2 (Fin 4 × Fin t) → ℝ) (u v : Fin 4 × Fin t) : ℝ :=
  if u.1 = v.1 then
    (if u.2 = v.2 then 0 else cI x u.1 + Pc x u.1 u.2 + Pc x u.1 v.2 + zI x u.1 u.2 v.2 / (2 * t))
  else if Opp u.1 v.1 then
    cC x u.1 v.1 + Qc x u.1 u.2 v.1 + Qc x v.1 v.2 u.1 + zC x u.1 u.2 v.1 v.2 / (2 * t - 4)
  else 0

/-! ### Symmetry and the operator `R` -/

theorem mC_symm (x : Sym2 (Fin 4 × Fin t) → ℝ) (i j : Fin 4) : mC x i j = mC x j i := by
  unfold mC rC
  rw [sum_comm]
  simp_rw [Sym2.eq_swap (a := (i, _))]

theorem zI_symm (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a b : Fin t) :
    zI x i a b = zI x i b a := by
  unfold zI; rw [Sym2.eq_swap]; ring

theorem zC_symm (x : Sym2 (Fin 4 × Fin t) → ℝ) (i : Fin 4) (a : Fin t) (j : Fin 4) (b : Fin t) :
    zC x i a j b = zC x j b i a := by
  unfold zC; rw [Sym2.eq_swap, mC_symm]; ring

theorem Rf_symm (x : Sym2 (Fin 4 × Fin t) → ℝ) (u v : Fin 4 × Fin t) : Rf x u v = Rf x v u := by
  unfold Rf
  by_cases h : u.1 = v.1
  · rw [if_pos h, if_pos h.symm]
    by_cases h2 : u.2 = v.2
    · rw [if_pos h2, if_pos h2.symm]
    · rw [if_neg h2, if_neg (Ne.symm h2), zI_symm, h]; ring
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases ho : Opp u.1 v.1
    · rw [if_pos ho, if_pos (opp_symm ho), zC_symm, cC, cC, crossCoef_symm]; ring
    · rw [if_neg ho, if_neg (fun h' => ho (opp_symm h'))]

/-- The right inverse as a function of edges. -/
noncomputable def Rv (x : Sym2 (Fin 4 × Fin t) → ℝ) : Sym2 (Fin 4 × Fin t) → ℝ :=
  fun e => Sym2.lift ⟨Rf x, Rf_symm x⟩ e

theorem Rv_mk (x : Sym2 (Fin 4 × Fin t) → ℝ) (u v : Fin 4 × Fin t) :
    Rv x s(u, v) = Rf x u v := rfl

theorem Rv_diag (x : Sym2 (Fin 4 × Fin t) → ℝ) (a : Fin 4 × Fin t) : Rv x s(a, a) = 0 := by
  simp [Rv_mk, Rf]

/-! ### Vanishing class sums and row sums -/

section Identities

variable (x : Sym2 (Fin 4 × Fin t) → ℝ)

theorem sum_aC (ht : 4 ≤ t) (i : Fin 4) : ∑ a, aC x i a = 0 := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (t : ℝ) * (t - 1) ≠ 0 := by
    apply mul_ne_zero <;> linarith
  have h1 : (t : ℝ) - 1 ≠ 0 := by linarith
  have ht0 : (t : ℝ) ≠ 0 := by linarith
  have hm : (t : ℝ) * (t - 1) * mI x i = ∑ a, rI x i a := by unfold mI; field_simp
  simp only [aC, ← sum_div, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [div_eq_zero_iff]; left
  linear_combination -hm

theorem sum_bC (ht : 4 ≤ t) (i : Fin 4) (j : Fin 4) : ∑ a, bC x i a j = 0 := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (t : ℝ) ≠ 0 := by linarith
  simp only [bC, sum_sub_distrib, ← sum_div, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, mC]
  field_simp
  ring

theorem sum_Pc (ht : 4 ≤ t) (i : Fin 4) : ∑ a, Pc x i a = 0 := by
  simp only [Pc, starInternal, ← sum_div, sum_sub_distrib, ← mul_sum, sum_add_distrib,
    sum_aC x ht, sum_bC x ht]
  simp

theorem sum_Qc (ht : 4 ≤ t) (i : Fin 4) (j : Fin 4) : ∑ a, Qc x i a j = 0 := by
  simp only [Qc, ← sum_div, sum_sub_distrib, ← mul_sum, sum_bC x ht, sum_Pc x ht]
  simp

theorem rowsum_zI (ht : 4 ≤ t) (i : Fin 4) (a : Fin t) :
    (∑ b, if b = a then 0 else zI x i a b) = 0 := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h2 : (t : ℝ) - 2 ≠ 0 := by linarith
  have hsplit : ∀ b, (if b = a then 0 else zI x i a b) =
      (if b = a then 0 else x s((i, a), (i, b))) -
        (if b = a then 0 else (mI x i + aC x i a + aC x i b)) := by
    intro b; split_ifs <;> simp [zI]; ring
  rw [sum_congr rfl fun b _ => hsplit b, sum_sub_distrib,
    sum_ne_index (fun b => mI x i + aC x i a + aC x i b)]
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_aC x ht]
  have haC : aC x i a * (t - 2) = rI x i a - (t - 1) * mI x i := by
    unfold aC; field_simp
  change rI x i a - _ = 0
  linear_combination -haC

theorem rowsum_zC (ht : 4 ≤ t) (i : Fin 4) (a : Fin t) (j : Fin 4) :
    (∑ b, zC x i a j b) = 0 := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (t : ℝ) ≠ 0 := by linarith
  simp only [zC, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    sum_bC x ht]
  change rC x i a j - _ - _ - 0 = 0
  unfold bC; field_simp; ring

/-! ### Row sums of `R x` -/

theorem rowF_Rv_own (ht : 4 ≤ t) (i : Fin 4) (a : Fin t) :
    rowF (Rv x) (i, a) i = (t - 1) * cI x i + (t - 2) * Pc x i a := by
  unfold rowF
  simp only [Rv_mk, Rf, if_true]
  have hsplit : ∀ k : Fin t, (if a = k then 0 else
      cI x i + Pc x i a + Pc x i k + zI x i a k / (2 * t)) =
      (if k = a then 0 else cI x i + Pc x i a) + (if k = a then 0 else Pc x i k) +
        (if k = a then 0 else zI x i a k) / (2 * t) := by
    intro k
    by_cases h : k = a
    · subst h; simp
    · rw [if_neg (Ne.symm h), if_neg h, if_neg h, if_neg h]
  rw [sum_congr rfl fun k _ => hsplit k, sum_add_distrib, sum_add_distrib, ← sum_div,
    rowsum_zI x ht, sum_ne_index, sum_ne_index, sum_Pc x ht]
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem rowF_Rv_opp (ht : 4 ≤ t) (i : Fin 4) (a : Fin t) (j : Fin 4) (h : Opp i j) :
    rowF (Rv x) (i, a) j = t * cC x i j + t * Qc x i a j := by
  unfold rowF
  simp only [Rv_mk, Rf, if_neg (opp_ne h), if_pos h]
  simp only [sum_add_distrib, ← sum_div, rowsum_zC x ht, sum_Qc x ht, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ### The right-inverse identity -/

theorem intCoef_blocksOf (i : Fin 4) : intCoef (blocksOf x) i = mI x i / (2 * t) := by
  fin_cases i <;> rfl

theorem crossCoef_blocksOf (i j : Fin 4) (h : Opp i j) :
    crossCoef (blocksOf x) i j = mC x i j / (t - 1) := by
  fin_cases i <;> fin_cases j <;> simp [Opp] at h <;>
    simp [crossCoef, blocksOf, mC_symm x 2 0, mC_symm x 2 1, mC_symm x 3 0, mC_symm x 3 1]

theorem block_int_eq (hb : (blocksOf x).Balanced) (i : Fin 4) :
    cI x i + cC x i (first1 i) + cC x i (second1 i) = mI x i / (2 * t) := by
  rw [← intCoef_blocksOf, ← blockMap_inverse _ hb, blockMap_int]; rfl

theorem block_cross_eq (hb : (blocksOf x).Balanced) (i j : Fin 4) (h : Opp i j) :
    cI x i + cI x j + 4 * cC x i j = mC x i j / (t - 1) := by
  rw [← crossCoef_blocksOf x i j h, ← blockMap_inverse _ hb, blockMap_cross _ i j h]; rfl

theorem star_eq (ht : 4 ≤ t) (i : Fin 4) (a : Fin t) :
    2 * t * Pc x i a + t * (Qc x i a (first1 i) + Qc x i a (second1 i)) = aC x i a := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h := (star_inverse t (aC x i a) (bC x i a (first1 i)) (bC x i a (second1 i)) ht').1
  have hs : starInternal t (aC x i a) (bC x i a (second1 i)) (bC x i a (first1 i)) =
      starInternal t (aC x i a) (bC x i a (first1 i)) (bC x i a (second1 i)) := by
    simp only [starInternal, add_comm (bC x i a (second1 i))]
  have e2 : Qc x i a (second1 i) =
      starCross t (aC x i a) (bC x i a (second1 i)) (bC x i a (first1 i)) := by
    simp only [Qc, starCross, hs, Pc]
  rw [e2]
  exact h

theorem star_cross_eq (ht : 4 ≤ t) (i : Fin 4) (a : Fin t) (j : Fin 4) :
    (3 * t - 4) * Qc x i a j + (t - 2) * Pc x i a = bC x i a j := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h3 : (3 * t - 4 : ℝ) ≠ 0 := by linarith
  unfold Qc; field_simp; ring

/-- **`R` is a right inverse of the real Gram operator on internal edges.** -/
theorem gram_Rv_internal (ht : 4 ≤ t) (hb : (blocksOf x).Balanced) (i : Fin 4) (a b : Fin t)
    (hab : a ≠ b) : gram (Rv x) s((i, a), (i, b)) = x s((i, a), (i, b)) := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h0 : (t : ℝ) ≠ 0 := by linarith
  have huv : ((i, a) : Fin 4 × Fin t) ≠ (i, b) := fun e => hab (Prod.ext_iff.mp e).2
  rw [gram_internal _ _ _ huv rfl]
  simp only [Rv_mk, Rf, if_true, if_neg hab]
  rw [rowF_Rv_opp x ht i a _ (opp_first1 i), rowF_Rv_opp x ht i b _ (opp_first1 i),
    rowF_Rv_opp x ht i a _ (opp_second1 i), rowF_Rv_opp x ht i b _ (opp_second1 i)]
  have e1 := block_int_eq x hb i
  have e2 := star_eq x ht i a
  have e3 := star_eq x ht i b
  have e4 : 2 * (t : ℝ) * (zI x i a b / (2 * t)) = zI x i a b := by field_simp
  have e5 : 2 * (t : ℝ) * (mI x i / (2 * t)) = mI x i := by field_simp
  have e6 : zI x i a b = x s((i, a), (i, b)) - mI x i - aC x i a - aC x i b := rfl
  linear_combination (2 * (t : ℝ)) * e1 + e2 + e3 + e4 + e5 + e6

/-- **`R` is a right inverse of the real Gram operator on cross edges.** -/
theorem gram_Rv_cross (ht : 4 ≤ t) (hb : (blocksOf x).Balanced) (i : Fin 4) (a : Fin t)
    (j : Fin 4) (b : Fin t) (h : Opp i j) :
    gram (Rv x) s((i, a), (j, b)) = x s((i, a), (j, b)) := by
  have ht' : (4 : ℝ) ≤ t := by exact_mod_cast ht
  have h1 : (t : ℝ) - 1 ≠ 0 := by linarith
  have h4 : (2 * t - 4 : ℝ) ≠ 0 := by linarith
  rw [gram_cross _ (Rv_diag x) _ _ h]
  simp only [Rv_mk, Rf, if_neg (opp_ne h), if_pos h]
  rw [rowF_Rv_own x ht i a, rowF_Rv_own x ht j b, rowF_Rv_opp x ht i a j h,
    rowF_Rv_opp x ht j b i (opp_symm h)]
  have e1 := block_cross_eq x hb i j h
  have e2 := star_cross_eq x ht i a j
  have e3 := star_cross_eq x ht j b i
  have e4 : (2 * t - 4 : ℝ) * (zC x i a j b / (2 * t - 4)) = zC x i a j b := by field_simp
  have e5 : ((t : ℝ) - 1) * (mC x i j / (t - 1)) = mC x i j := by field_simp
  have e6 : cC x j i = cC x i j := by unfold cC; rw [crossCoef_symm]
  have e7 : zC x i a j b = x s((i, a), (j, b)) - mC x i j - bC x i a j - bC x j b i := rfl
  rw [e6]
  linear_combination ((t : ℝ) - 1) * e1 + e2 + e3 + e4 + e5 + e7

end Identities

end PartitionedTriangleAbsorption.F1TemplateStage233
