/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalVertexModes

/-! # Uniform physical lifts of the global class totals -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer

variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

def classTotal (p : V → Fin t) (g : V → V → ℝ) (i j : Fin t) : ℝ :=
  ∑ a ∈ classVertices p i, classRow p g a j

theorem classTotal_add (p : V → Fin t) (g h : V → V → ℝ) (i j : Fin t) :
    classTotal p (fun a b => g a b + h a b) i j = classTotal p g i j + classTotal p h i j := by
  simp only [classTotal, classRow_add, sum_add_distrib]

theorem classTotal_sub (p : V → Fin t) (g h : V → V → ℝ) (i j : Fin t) :
    classTotal p (fun a b => g a b - h a b) i j = classTotal p g i j - classTotal p h i j := by
  simp only [classTotal, classRow, sum_sub_distrib]

theorem classTotal_symmetric (p : V → Fin t) (g : V → V → ℝ) (hs : ∀ a b, g a b = g b a)
    (i j : Fin t) : classTotal p g i j = classTotal p g j i := by
  unfold classTotal classRow
  rw [sum_comm]
  exact sum_congr rfl (fun b _ => sum_congr rfl (fun a _ => hs a b))

def constClassBlock (p : V → Fin t) (i j : Fin t) (x : ℝ) (a b : V) : ℝ :=
  if p a = i ∧ p b = j then x else 0

def constInternalBlock (p : V → Fin t) (i : Fin t) (x : ℝ) (a b : V) : ℝ :=
  if p a = i ∧ p b = i then if a ≠ b then x else 0 else 0

theorem classTotal_constClassBlock (p : V → Fin t) (i j : Fin t) (x : ℝ) (k l : Fin t) :
    classTotal p (constClassBlock p i j x) k l =
      if k = i ∧ l = j then classSize p i * classSize p j * x else 0 := by
  unfold classTotal constClassBlock
  simp only [classRow_mask]
  by_cases hl : l = j
  · simp only [hl, and_true]
    rw [sum_class_indicator]
    by_cases hk : k = i
    · simp only [hk, ite_true, sum_const, nsmul_eq_mul]
      change classSize p i * (classSize p j * x) = classSize p i * classSize p j * x
      ring
    · simp [hk]
  · simp [hl]

theorem classRow_constInternalBlock (p : V → Fin t) (i : Fin t) (x : ℝ) (a : V) (k : Fin t) :
    classRow p (constInternalBlock p i x) a k =
      if p a = i ∧ k = i then (classSize p i - 1) * x else 0 := by
  unfold constInternalBlock
  rw [classRow_mask]
  split_ifs with h
  · exact class_excluding_const p i a h.1 x
  · rfl

theorem classTotal_constInternalBlock (p : V → Fin t) (i : Fin t) (x : ℝ) (k l : Fin t) :
    classTotal p (constInternalBlock p i x) k l =
      if k = i ∧ l = i then classSize p i * (classSize p i - 1) * x else 0 := by
  unfold classTotal
  simp only [classRow_constInternalBlock]
  by_cases hl : l = i
  · simp only [hl, and_true]
    rw [sum_class_indicator]
    by_cases hk : k = i
    · simp only [hk, ite_true, sum_const, nsmul_eq_mul]
      change classSize p i * ((classSize p i - 1) * x) = classSize p i * (classSize p i - 1) * x
      ring
    · simp [hk]
  · simp [hl]

def repeatedTypeWeight (p : V → Fin t) (i j : Fin t) (z : ℝ) : V → V → V → ℝ :=
  aabLift p i j (fun _a _b _c =>
    2 * z / (classSize p i * (classSize p i - 1) * classSize p j))

def tripartiteTypeWeight (p : V → Fin t) (i j k : Fin t) (z : ℝ) : V → V → V → ℝ :=
  abcLift p i j k (fun _a _b _c => z / (classSize p i * classSize p j * classSize p k))

theorem repeatedTypeWeight_symmetric (p : V → Fin t) (i j : Fin t) (z : ℝ) :
    TernarySymmetric (repeatedTypeWeight p i j z) := aabLift_symmetric p i j _ (by intros; rfl)

theorem tripartiteTypeWeight_symmetric (p : V → Fin t) (i j k : Fin t) (z : ℝ) :
    TernarySymmetric (tripartiteTypeWeight p i j k z) := abcLift_symmetric p i j k _

theorem repeatedTypeWeight_load (p : V → Fin t) (i j : Fin t) (z : ℝ)
    (hi : classSize p i ≠ 0) (hi1 : classSize p i - 1 ≠ 0) (hj : classSize p j ≠ 0) (a b : V) :
    ternaryLoad (repeatedTypeWeight p i j z) a b =
      constInternalBlock p i (2 * z / (classSize p i * (classSize p i - 1))) a b +
      constClassBlock p i j (2 * z / (classSize p i * classSize p j)) a b +
      constClassBlock p j i (2 * z / (classSize p i * classSize p j)) a b := by
  have ht : (∑ c ∈ classVertices p j,
      2 * z / (classSize p i * (classSize p i - 1) * classSize p j)) =
      2 * z / (classSize p i * (classSize p i - 1)) := by
    simp only [div_mul_eq_div_div]
    exact class_uniform_sum p j _ hj
  have hc (a : V) (ha : p a = i) :
      (∑ c ∈ classVertices p i, if a ≠ c then
        2 * z / (classSize p i * (classSize p i - 1) * classSize p j) else 0) =
        2 * z / (classSize p i * classSize p j) := by
    rw [class_excluding_const p i a ha]
    field_simp
  have hleft :
      (if p a = i ∧ p b = j then ∑ c ∈ classVertices p i, if a ≠ c then
        2 * z / (classSize p i * (classSize p i - 1) * classSize p j) else 0 else 0) =
      if p a = i ∧ p b = j then 2 * z / (classSize p i * classSize p j) else 0 := by
    split_ifs with h
    · exact hc a h.1
    · rfl
  have hright :
      (if p b = i ∧ p a = j then ∑ c ∈ classVertices p i, if b ≠ c then
        2 * z / (classSize p i * (classSize p i - 1) * classSize p j) else 0 else 0) =
      if p b = i ∧ p a = j then 2 * z / (classSize p i * classSize p j) else 0 := by
    split_ifs with h
    · exact hc b h.1
    · rfl
  rw [repeatedTypeWeight, aabLift_load]
  simp only [ht]
  rw [hleft, hright]
  unfold constInternalBlock constClassBlock
  by_cases ha : p a = i <;> by_cases hb : p b = i <;>
    by_cases haj : p a = j <;> by_cases hbj : p b = j <;> by_cases hab : a = b <;>
    simp [ha, hb, haj, hbj, hab, and_comm]

theorem repeatedTypeWeight_totals (p : V → Fin t) (i j : Fin t) (z : ℝ)
    (hi : classSize p i ≠ 0) (hi1 : classSize p i - 1 ≠ 0) (hj : classSize p j ≠ 0) (k l : Fin t) :
    classTotal p (ternaryLoad (repeatedTypeWeight p i j z)) k l =
      (if k = i ∧ l = i then 2 * z else 0) +
      (if k = i ∧ l = j then 2 * z else 0) +
      (if k = j ∧ l = i then 2 * z else 0) := by
  have he : ternaryLoad (repeatedTypeWeight p i j z) = fun a b =>
      constInternalBlock p i (2 * z / (classSize p i * (classSize p i - 1))) a b +
      constClassBlock p i j (2 * z / (classSize p i * classSize p j)) a b +
      constClassBlock p j i (2 * z / (classSize p i * classSize p j)) a b := by
    funext a b
    exact repeatedTypeWeight_load p i j z hi hi1 hj a b
  rw [he, classTotal_add, classTotal_add, classTotal_constInternalBlock,
    classTotal_constClassBlock, classTotal_constClassBlock]
  have h0 : classSize p i * (classSize p i - 1) *
      (2 * z / (classSize p i * (classSize p i - 1))) = 2 * z := by field_simp
  have h1 : classSize p i * classSize p j * (2 * z / (classSize p i * classSize p j)) = 2 * z := by
    field_simp
  have h2 : classSize p j * classSize p i * (2 * z / (classSize p i * classSize p j)) = 2 * z := by
    field_simp
  rw [h0, h1, h2]

theorem classTotal_normalizedBlock (p : V → Fin t) (i j : Fin t) (z : ℝ)
    (hi : classSize p i ≠ 0) (hj : classSize p j ≠ 0) (k l : Fin t) :
    classTotal p (constClassBlock p i j (z / (classSize p i * classSize p j))) k l =
      if k = i ∧ l = j then z else 0 := by
  rw [classTotal_constClassBlock]
  have h : classSize p i * classSize p j * (z / (classSize p i * classSize p j)) = z := by
    field_simp
  rw [h]

theorem tripartiteTypeWeight_load (p : V → Fin t) (i j k : Fin t) (z : ℝ)
    (hi : classSize p i ≠ 0) (hj : classSize p j ≠ 0) (hk : classSize p k ≠ 0) (a b : V) :
    ternaryLoad (tripartiteTypeWeight p i j k z) a b =
      constClassBlock p i j (z / (classSize p i * classSize p j)) a b +
      constClassBlock p j i (z / (classSize p j * classSize p i)) a b +
      constClassBlock p i k (z / (classSize p i * classSize p k)) a b +
      constClassBlock p k i (z / (classSize p k * classSize p i)) a b +
      constClassBlock p j k (z / (classSize p j * classSize p k)) a b +
      constClassBlock p k j (z / (classSize p k * classSize p j)) a b := by
  have h0 : (∑ c ∈ classVertices p i, z / (classSize p i * classSize p j * classSize p k)) =
      z / (classSize p j * classSize p k) := by
    rw [sum_const, nsmul_eq_mul]
    change classSize p i * (z / (classSize p i * classSize p j * classSize p k)) = _
    field_simp
  have h1 : (∑ c ∈ classVertices p j, z / (classSize p i * classSize p j * classSize p k)) =
      z / (classSize p i * classSize p k) := by
    rw [sum_const, nsmul_eq_mul]
    change classSize p j * (z / (classSize p i * classSize p j * classSize p k)) = _
    field_simp
  have h2 : (∑ c ∈ classVertices p k, z / (classSize p i * classSize p j * classSize p k)) =
      z / (classSize p i * classSize p j) := by
    simp only [div_mul_eq_div_div]
    exact class_uniform_sum p k _ hk
  rw [tripartiteTypeWeight, abcLift_load]
  simp only [h0, h1, h2, constClassBlock, @and_comm (p b = i) (p a = j),
    @and_comm (p b = i) (p a = k), @and_comm (p b = j) (p a = k), mul_comm]
  ring

theorem tripartiteTypeWeight_totals (p : V → Fin t) (i j k : Fin t) (z : ℝ)
    (hi : classSize p i ≠ 0) (hj : classSize p j ≠ 0) (hk : classSize p k ≠ 0) (l m : Fin t) :
    classTotal p (ternaryLoad (tripartiteTypeWeight p i j k z)) l m =
      (if l = i ∧ m = j then z else 0) + (if l = j ∧ m = i then z else 0) +
      (if l = i ∧ m = k then z else 0) + (if l = k ∧ m = i then z else 0) +
      (if l = j ∧ m = k then z else 0) + (if l = k ∧ m = j then z else 0) := by
  have he : ternaryLoad (tripartiteTypeWeight p i j k z) = fun a b =>
      constClassBlock p i j (z / (classSize p i * classSize p j)) a b +
      constClassBlock p j i (z / (classSize p j * classSize p i)) a b +
      constClassBlock p i k (z / (classSize p i * classSize p k)) a b +
      constClassBlock p k i (z / (classSize p k * classSize p i)) a b +
      constClassBlock p j k (z / (classSize p j * classSize p k)) a b +
      constClassBlock p k j (z / (classSize p k * classSize p j)) a b := by
    funext a b
    exact tripartiteTypeWeight_load p i j k z hi hj hk a b
  rw [he]
  simp only [classTotal_add, classTotal_normalizedBlock p i j z hi hj,
    classTotal_normalizedBlock p j i z hj hi, classTotal_normalizedBlock p i k z hi hk,
    classTotal_normalizedBlock p k i z hk hi, classTotal_normalizedBlock p j k z hj hk,
    classTotal_normalizedBlock p k j z hk hj]

theorem repeatedType_normalizer_bound (p : V → Fin t) (i j : Fin t) (z E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz : |z| ≤ 8 * E) (hm : ∀ i, δ ≤ classSize p i) :
    |2 * z / (classSize p i * (classSize p i - 1) * classSize p j)| ≤ 32 * E / δ ^ 3 := by
  have hd : 0 < δ := by linarith
  have hpos (i : Fin t) : 0 < classSize p i := lt_of_lt_of_le hd (hm i)
  have hpos1 : 0 < classSize p i - 1 := by have := hm i; linarith
  have hhalf : δ / 2 ≤ classSize p i - 1 := by have := hm i; linarith
  have hdenpos : 0 < classSize p i * (classSize p i - 1) * classSize p j :=
    mul_pos (mul_pos (hpos i) hpos1) (hpos j)
  have hden : δ ^ 3 ≤ 2 * (classSize p i * (classSize p i - 1) * classSize p j) := by
    have h1 := mul_le_mul (hm i) hhalf (by positivity : 0 ≤ δ / 2) (hpos i).le
    have h2 := mul_le_mul h1 (hm j) hd.le (mul_pos (hpos i) hpos1).le
    nlinarith
  have hnum : |2 * z| ≤ 16 * E := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith
  apply (uniform_bound (2 * z) (16 * E) _ hnum hdenpos).trans
  rw [div_le_div_iff₀ hdenpos (pow_pos hd 3)]
  nlinarith [mul_nonneg hE (sub_nonneg.mpr hden)]

theorem tripartiteType_normalizer_bound (p : V → Fin t) (i j k : Fin t) (z E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hz : |z| ≤ 8 * E) (hm : ∀ i, δ ≤ classSize p i) :
    |z / (classSize p i * classSize p j * classSize p k)| ≤ 32 * E / δ ^ 3 := by
  have hd : 0 < δ := by linarith
  have hpos (i : Fin t) : 0 < classSize p i := lt_of_lt_of_le hd (hm i)
  have hdenpos : 0 < classSize p i * classSize p j * classSize p k :=
    mul_pos (mul_pos (hpos i) (hpos j)) (hpos k)
  have hden : δ ^ 3 ≤ classSize p i * classSize p j * classSize p k := by
    have h1 := mul_le_mul (hm i) (hm j) hd.le (hpos i).le
    have h2 := mul_le_mul h1 (hm k) hd.le (mul_pos (hpos i) (hpos j)).le
    nlinarith
  apply (uniform_bound z (8 * E) _ hz hdenpos).trans
  rw [div_le_div_iff₀ hdenpos (pow_pos hd 3)]
  nlinarith [mul_nonneg hE (sub_nonneg.mpr hden), mul_nonneg hE hdenpos.le]

theorem classTotal_ternary_add (p : V → Fin t) (w w' : V → V → V → ℝ) (i j : Fin t) :
    classTotal p (ternaryLoad (fun a b c => w a b c + w' a b c)) i j =
      classTotal p (ternaryLoad w) i j + classTotal p (ternaryLoad w') i j := by
  simp only [classTotal, classRow_ternary_add, sum_add_distrib]

#print axioms repeatedTypeWeight_load
#print axioms repeatedTypeWeight_totals
#print axioms tripartiteTypeWeight_load
#print axioms tripartiteTypeWeight_totals
#print axioms repeatedType_normalizer_bound
#print axioms tripartiteType_normalizer_bound

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
