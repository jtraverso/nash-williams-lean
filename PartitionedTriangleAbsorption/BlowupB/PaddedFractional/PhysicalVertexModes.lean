/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalEdgeModes

@[expose] public section

/-! # Physical corrections of vertex-to-class rows -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer

variable {V : Type*} {t : ℕ} [Fintype V] [DecidableEq V]

def classRow (p : V → Fin t) (g : V → V → ℝ) (a : V) (k : Fin t) : ℝ :=
  ∑ b ∈ classVertices p k, g a b

theorem classRow_add (p : V → Fin t) (g h : V → V → ℝ) (a : V) (k : Fin t) :
    classRow p (fun a b => g a b + h a b) a k = classRow p g a k + classRow p h a k := by
  simp only [classRow, sum_add_distrib]

theorem classRow_smul (p : V → Fin t) (g : V → V → ℝ) (x : ℝ) (a : V) (k : Fin t) :
    classRow p (fun a b => x * g a b) a k = x * classRow p g a k := by
  simp only [classRow, mul_sum]

theorem sum_class_indicator (p : V → Fin t) (j k : Fin t) (f : V → ℝ) :
    (∑ b ∈ classVertices p k, if p b = j then f b else 0) =
      if k = j then ∑ b ∈ classVertices p j, f b else 0 := by
  by_cases hkj : k = j
  · subst k
    simp only [ite_true]
    apply sum_congr rfl
    intro b hb
    simp only [(mem_classVertices p j b).mp hb, ite_true]
  · simp only [hkj, ite_false]
    apply sum_eq_zero
    intro b hb
    simp only [(mem_classVertices p k b).mp hb, hkj, ite_false]

theorem classRow_mask (p : V → Fin t) (i j : Fin t) (g : V → V → ℝ) (a : V) (k : Fin t) :
    classRow p (fun a b => if p a = i ∧ p b = j then g a b else 0) a k =
      if p a = i ∧ k = j then ∑ b ∈ classVertices p j, g a b else 0 := by
  by_cases ha : p a = i <;> simp [classRow, ha, sum_class_indicator]

theorem class_uniform_sum (p : V → Fin t) (i : Fin t) (x : ℝ) (hi : classSize p i ≠ 0) :
    (∑ b ∈ classVertices p i, x / classSize p i) = x := by
  rw [sum_const, nsmul_eq_mul]
  change classSize p i * (x / classSize p i) = x
  field_simp

theorem sum_ite_div (S : Finset V) (P : V → Prop) [DecidablePred P] (f : V → ℝ) (d : ℝ) :
    (∑ c ∈ S, if P c then f c / d else 0) = (∑ c ∈ S, if P c then f c else 0) / d := by
  rw [sum_div]
  apply sum_congr rfl
  intro c hc
  by_cases h : P c <;> simp [h]

theorem class_excluding_const (p : V → Fin t) (i : Fin t) (a : V) (ha : p a = i) (x : ℝ) :
    (∑ b ∈ classVertices p i, if a ≠ b then x else 0) = (classSize p i - 1) * x := by
  rw [sum_ne_eq_erase]
  have he := sum_erase_add (classVertices p i) (fun _ => x)
    ((mem_classVertices p i a).mpr ha)
  have ht : (∑ b ∈ classVertices p i, x) = classSize p i * x := by
    rw [sum_const, nsmul_eq_mul]
    rfl
  rw [ht] at he
  linarith

def vertexCrossKernel (p : V → Fin t) (i j : Fin t) (f : V → ℝ) (a b : V) : ℝ :=
  (if p a = i ∧ p b = j then f a / classSize p j else 0) +
  (if p a = j ∧ p b = i then f b / classSize p j else 0)

def vertexInternalKernel (p : V → Fin t) (i : Fin t) (f : V → ℝ) (a b : V) : ℝ :=
  if p a = i ∧ p b = i then
    if a ≠ b then (f a + f b) / (classSize p i - 2) else 0 else 0

theorem classRow_vertexCrossKernel (p : V → Fin t) (i j : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0) (hj : classSize p j ≠ 0) (a : V) (k : Fin t) :
    classRow p (vertexCrossKernel p i j f) a k = if p a = i ∧ k = j then f a else 0 := by
  have hz : (∑ b ∈ classVertices p i, f b / classSize p j) = 0 := by
    rw [← sum_div, hf, zero_div]
  unfold vertexCrossKernel
  rw [classRow_add, classRow_mask, classRow_mask]
  simp only [class_uniform_sum p j _ hj, hz, ite_self, add_zero]

theorem classRow_vertexInternalKernel (p : V → Fin t) (i : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0) (hi : classSize p i - 2 ≠ 0) (a : V) (k : Fin t) :
    classRow p (vertexInternalKernel p i f) a k = if p a = i ∧ k = i then f a else 0 := by
  unfold vertexInternalKernel
  rw [classRow_mask]
  split_ifs with h
  · rw [sum_ite_div, class_repeated_numerator p i f hf a h.1]
    exact mul_div_cancel_left₀ _ hi
  · rfl

def repeatedVertexWeight (p : V → Fin t) (i j : Fin t) (f : V → ℝ) : V → V → V → ℝ :=
  aabLift p i j (fun a b _c => (f a + f b) / ((classSize p i - 2) * classSize p j))

theorem repeatedVertexWeight_symmetric (p : V → Fin t) (i j : Fin t) (f : V → ℝ) :
    TernarySymmetric (repeatedVertexWeight p i j f) := by
  apply aabLift_symmetric
  intro a b c
  rw [add_comm]

theorem repeatedVertexWeight_load (p : V → Fin t) (i j : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0)
    (hi : classSize p i - 2 ≠ 0) (hj : classSize p j ≠ 0) (a b : V) :
    ternaryLoad (repeatedVertexWeight p i j f) a b =
      vertexInternalKernel p i f a b + vertexCrossKernel p i j f a b := by
  have ht (a b : V) :
      (∑ c ∈ classVertices p j, (f a + f b) / ((classSize p i - 2) * classSize p j)) =
      (f a + f b) / (classSize p i - 2) := by
    simp only [div_mul_eq_div_div]
    exact class_uniform_sum p j _ hj
  have hc (a : V) (ha : p a = i) :
      (∑ c ∈ classVertices p i, if a ≠ c then
        (f a + f c) / ((classSize p i - 2) * classSize p j) else 0) = f a / classSize p j := by
    rw [sum_ite_div, class_repeated_numerator p i f hf a ha]
    field_simp
  have hleft :
      (if p a = i ∧ p b = j then
        ∑ c ∈ classVertices p i, if a ≠ c then
          (f a + f c) / ((classSize p i - 2) * classSize p j) else 0 else 0) =
      if p a = i ∧ p b = j then f a / classSize p j else 0 := by
    split_ifs with h
    · exact hc a h.1
    · rfl
  have hright :
      (if p b = i ∧ p a = j then
        ∑ c ∈ classVertices p i, if b ≠ c then
          (f b + f c) / ((classSize p i - 2) * classSize p j) else 0 else 0) =
      if p b = i ∧ p a = j then f b / classSize p j else 0 := by
    split_ifs with h
    · exact hc b h.1
    · rfl
  rw [repeatedVertexWeight, aabLift_load]
  simp only [ht]
  rw [hleft, hright]
  unfold vertexInternalKernel vertexCrossKernel
  by_cases ha : p a = i <;> by_cases hb : p b = i <;>
    by_cases haj : p a = j <;> by_cases hbj : p b = j <;> by_cases hab : a = b <;>
    simp [ha, hb, haj, hbj, hab, add_assoc, and_comm]

theorem repeatedVertexWeight_rows (p : V → Fin t) (i j : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0)
    (hi : classSize p i - 2 ≠ 0) (hj : classSize p j ≠ 0) (a : V) (k : Fin t) :
    classRow p (ternaryLoad (repeatedVertexWeight p i j f)) a k =
      (if p a = i ∧ k = i then f a else 0) + (if p a = i ∧ k = j then f a else 0) := by
  have he : ternaryLoad (repeatedVertexWeight p i j f) =
      fun a b => vertexInternalKernel p i f a b + vertexCrossKernel p i j f a b := by
    funext a b
    exact repeatedVertexWeight_load p i j f hf hi hj a b
  rw [he, classRow_add, classRow_vertexInternalKernel p i f hf hi,
    classRow_vertexCrossKernel p i j f hf hj]

def singletonVertexWeight (p : V → Fin t) (i j : Fin t) (f : V → ℝ) : V → V → V → ℝ :=
  aabLift p i j (fun _a _b c => 2 * f c / (classSize p i * (classSize p i - 1)))

theorem singletonVertexWeight_symmetric (p : V → Fin t) (i j : Fin t) (f : V → ℝ) :
    TernarySymmetric (singletonVertexWeight p i j f) := by
  apply aabLift_symmetric
  intro a b c
  rfl

theorem singletonVertexWeight_load (p : V → Fin t) (i j : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p j, f a = 0)
    (hi : classSize p i ≠ 0) (hi1 : classSize p i - 1 ≠ 0) (a b : V) :
    ternaryLoad (singletonVertexWeight p i j f) a b = 2 * vertexCrossKernel p j i f a b := by
  have hz : (∑ c ∈ classVertices p j, 2 * f c / (classSize p i * (classSize p i - 1))) = 0 := by
    rw [← sum_div, ← mul_sum, hf, mul_zero, zero_div]
  have hc (a b : V) (ha : p a = i) :
      (∑ c ∈ classVertices p i, if a ≠ c then
        2 * f b / (classSize p i * (classSize p i - 1)) else 0) = 2 * f b / classSize p i := by
    rw [class_excluding_const p i a ha]
    field_simp
  have hleft :
      (if p a = i ∧ p b = j then
        ∑ c ∈ classVertices p i, if a ≠ c then
          2 * f b / (classSize p i * (classSize p i - 1)) else 0 else 0) =
      if p a = i ∧ p b = j then 2 * f b / classSize p i else 0 := by
    split_ifs with h
    · exact hc a b h.1
    · rfl
  have hright :
      (if p b = i ∧ p a = j then
        ∑ c ∈ classVertices p i, if b ≠ c then
          2 * f a / (classSize p i * (classSize p i - 1)) else 0 else 0) =
      if p b = i ∧ p a = j then 2 * f a / classSize p i else 0 := by
    split_ifs with h
    · exact hc b a h.1
    · rfl
  rw [singletonVertexWeight, aabLift_load]
  simp only [hz, ite_self, zero_add]
  rw [hleft, hright]
  simp only [vertexCrossKernel, @and_comm (p b = i) (p a = j),
    mul_add, mul_ite, mul_zero, ← mul_div_assoc]
  ring

theorem singletonVertexWeight_rows (p : V → Fin t) (i j : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p j, f a = 0)
    (hi : classSize p i ≠ 0) (hi1 : classSize p i - 1 ≠ 0) (a : V) (k : Fin t) :
    classRow p (ternaryLoad (singletonVertexWeight p i j f)) a k =
      if p a = j ∧ k = i then 2 * f a else 0 := by
  have he : ternaryLoad (singletonVertexWeight p i j f) =
      fun a b => 2 * vertexCrossKernel p j i f a b := by
    funext a b
    exact singletonVertexWeight_load p i j f hf hi hi1 a b
  rw [he, classRow_smul, classRow_vertexCrossKernel p j i f hf hi]
  simp only [mul_ite, mul_zero]

def tripartiteVertexWeight (p : V → Fin t) (i j k : Fin t) (f : V → ℝ) : V → V → V → ℝ :=
  abcLift p i j k (fun a _b _c => f a / (classSize p j * classSize p k))

theorem tripartiteVertexWeight_symmetric (p : V → Fin t) (i j k : Fin t) (f : V → ℝ) :
    TernarySymmetric (tripartiteVertexWeight p i j k f) := abcLift_symmetric p i j k _

theorem tripartiteVertexWeight_load (p : V → Fin t) (i j k : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0)
    (hj : classSize p j ≠ 0) (hk : classSize p k ≠ 0) (a b : V) :
    ternaryLoad (tripartiteVertexWeight p i j k f) a b =
      vertexCrossKernel p i j f a b + vertexCrossKernel p i k f a b := by
  have hz : (∑ c ∈ classVertices p i, f c / (classSize p j * classSize p k)) = 0 := by
    rw [← sum_div, hf, zero_div]
  have hj' (a : V) : (∑ c ∈ classVertices p j, f a / (classSize p j * classSize p k)) =
      f a / classSize p k := by
    rw [mul_comm (classSize p j) (classSize p k)]
    simp only [div_mul_eq_div_div]
    exact class_uniform_sum p j _ hj
  have hk' (a : V) : (∑ c ∈ classVertices p k, f a / (classSize p j * classSize p k)) =
      f a / classSize p j := by
    simp only [div_mul_eq_div_div]
    exact class_uniform_sum p k _ hk
  rw [tripartiteVertexWeight, abcLift_load]
  simp only [hz, hj', hk', ite_self, add_zero]
  simp only [vertexCrossKernel, @and_comm (p b = i) (p a = j),
    @and_comm (p b = i) (p a = k)]
  ring

theorem tripartiteVertexWeight_rows (p : V → Fin t) (i j k : Fin t) (f : V → ℝ)
    (hf : ∑ a ∈ classVertices p i, f a = 0)
    (hj : classSize p j ≠ 0) (hk : classSize p k ≠ 0) (a : V) (l : Fin t) :
    classRow p (ternaryLoad (tripartiteVertexWeight p i j k f)) a l =
      (if p a = i ∧ l = j then f a else 0) + (if p a = i ∧ l = k then f a else 0) := by
  have he : ternaryLoad (tripartiteVertexWeight p i j k f) =
      fun a b => vertexCrossKernel p i j f a b + vertexCrossKernel p i k f a b := by
    funext a b
    exact tripartiteVertexWeight_load p i j k f hf hj hk a b
  rw [he, classRow_add, classRow_vertexCrossKernel p i j f hf hj,
    classRow_vertexCrossKernel p i k f hf hk]

theorem repeatedVertexWeight_bound (p : V → Fin t) (i j : Fin t) (f : V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hf : ∀ a, |f a| ≤ D) (hi : 0 < classSize p i - 2) (hj : 0 < classSize p j)
    (a b c : V) :
    |repeatedVertexWeight p i j f a b c| ≤ 6 * D / ((classSize p i - 2) * classSize p j) := by
  have hden := mul_pos hi hj
  have h := aabLift_bound p i j
    (fun a b _c => (f a + f b) / ((classSize p i - 2) * classSize p j))
    (2 * D / ((classSize p i - 2) * classSize p j)) (by positivity)
    (fun a b _c => repeated_bound _ _ D _ (hf a) (hf b) hden) a b c
  calc
    _ ≤ 3 * (2 * D / ((classSize p i - 2) * classSize p j)) := h
    _ = 6 * D / ((classSize p i - 2) * classSize p j) := by ring

theorem singletonVertexWeight_bound (p : V → Fin t) (i j : Fin t) (f : V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hf : ∀ a, |f a| ≤ D) (hi : 0 < classSize p i) (hi1 : 0 < classSize p i - 1)
    (a b c : V) :
    |singletonVertexWeight p i j f a b c| ≤ 6 * D / (classSize p i * (classSize p i - 1)) := by
  have hden := mul_pos hi hi1
  have hb (c : V) : |2 * f c| ≤ 2 * D := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact mul_le_mul_of_nonneg_left (hf c) (by norm_num)
  have h := aabLift_bound p i j
    (fun _a _b c => 2 * f c / (classSize p i * (classSize p i - 1)))
    (2 * D / (classSize p i * (classSize p i - 1))) (by positivity)
    (fun _a _b c => uniform_bound _ (2 * D) _ (hb c) hden) a b c
  calc
    _ ≤ 3 * (2 * D / (classSize p i * (classSize p i - 1))) := h
    _ = 6 * D / (classSize p i * (classSize p i - 1)) := by ring

theorem tripartiteVertexWeight_bound (p : V → Fin t) (i j k : Fin t) (f : V → ℝ) (D : ℝ)
    (hD : 0 ≤ D) (hf : ∀ a, |f a| ≤ D) (hj : 0 < classSize p j) (hk : 0 < classSize p k)
    (a b c : V) :
    |tripartiteVertexWeight p i j k f a b c| ≤ 6 * D / (classSize p j * classSize p k) := by
  have hden := mul_pos hj hk
  have h := abcLift_bound p i j k
    (fun a _b _c => f a / (classSize p j * classSize p k))
    (D / (classSize p j * classSize p k)) (by positivity)
    (fun a _b _c => uniform_bound _ D _ (hf a) hden) a b c
  calc
    _ ≤ 6 * (D / (classSize p j * classSize p k)) := h
    _ = 6 * D / (classSize p j * classSize p k) := by ring

theorem vertexMode_bounds (p : V → Fin t) (f : V → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hf : ∀ a, |f a| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    (∀ i j, |repeatedVertexWeight p i j f a b c| ≤ 12 * D / δ ^ 2) ∧
    (∀ i j, |singletonVertexWeight p i j f a b c| ≤ 12 * D / δ ^ 2) ∧
    (∀ i j k, |tripartiteVertexWeight p i j k f a b c| ≤ 12 * D / δ ^ 2) := by
  have hd : 0 < δ := by linarith
  have hpos (i : Fin t) : 0 < classSize p i := lt_of_lt_of_le hd (hm i)
  have hpos1 (i : Fin t) : 0 < classSize p i - 1 := by have := hm i; linarith
  have hpos2 (i : Fin t) : 0 < classSize p i - 2 := by have := hm i; linarith
  have hhalf1 (i : Fin t) : δ / 2 ≤ classSize p i - 1 := by have := hm i; linarith
  have hhalf2 (i : Fin t) : δ / 2 ≤ classSize p i - 2 := by have := hm i; linarith
  have hnum (d : ℝ) (hposd : 0 < d) (hden : δ ^ 2 ≤ 2 * d) :
      6 * D / d ≤ 12 * D / δ ^ 2 := by
    rw [div_le_div_iff₀ hposd (sq_pos_of_pos hd)]
    nlinarith [mul_nonneg hD (sub_nonneg.mpr hden)]
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    apply (repeatedVertexWeight_bound p i j f D hD hf (hpos2 i) (hpos j) a b c).trans
    apply hnum _ (mul_pos (hpos2 i) (hpos j))
    have := mul_le_mul (hhalf2 i) (hm j) hd.le (hpos2 i).le
    nlinarith
  · intro i j
    apply (singletonVertexWeight_bound p i j f D hD hf (hpos i) (hpos1 i) a b c).trans
    apply hnum _ (mul_pos (hpos i) (hpos1 i))
    have := mul_le_mul (hm i) (hhalf1 i) (by positivity : 0 ≤ δ / 2) (hpos i).le
    nlinarith
  · intro i j k
    apply (tripartiteVertexWeight_bound p i j k f D hD hf (hpos j) (hpos k) a b c).trans
    apply hnum _ (mul_pos (hpos j) (hpos k))
    have := mul_le_mul (hm j) (hm k) hd.le (hpos j).le
    nlinarith [mul_pos (hpos j) (hpos k)]

theorem classRow_ternary_add (p : V → Fin t) (w w' : V → V → V → ℝ) (a : V) (k : Fin t) :
    classRow p (ternaryLoad (fun a b c => w a b c + w' a b c)) a k =
      classRow p (ternaryLoad w) a k + classRow p (ternaryLoad w') a k := by
  simp only [classRow, ternaryLoad, sum_add_distrib]

theorem TernarySymmetric.sum {ι : Type*} [Fintype ι] (w : ι → V → V → V → ℝ)
    (hw : ∀ i, TernarySymmetric (w i)) : TernarySymmetric (fun a b c => ∑ i, w i a b c) := by
  constructor
  · intro a b c
    exact sum_congr rfl (fun i _ => (hw i).1 a b c)
  · intro a b c
    exact sum_congr rfl (fun i _ => (hw i).2 a b c)

theorem TernarySupported.sum {ι : Type*} [Fintype ι] (p : V → Fin t)
    (F : Finset (Multiset (Fin t))) (w : ι → V → V → V → ℝ)
    (hw : ∀ i, TernarySupported p F (w i)) :
    TernarySupported p F (fun a b c => ∑ i, w i a b c) := by
  intro a b c hbad
  exact sum_eq_zero (fun i _ => hw i a b c hbad)

theorem classRow_ternary_sum {ι : Type*} [Fintype ι] (p : V → Fin t)
    (w : ι → V → V → V → ℝ) (a : V) (k : Fin t) :
    classRow p (ternaryLoad (fun a b c => ∑ i, w i a b c)) a k =
      ∑ i, classRow p (ternaryLoad (w i)) a k := by
  unfold classRow ternaryLoad
  calc
    _ = ∑ b ∈ classVertices p k, ∑ i, ∑ c, w i a b c := by
      apply sum_congr rfl
      intro b hb
      rw [sum_comm]
    _ = _ := by rw [sum_comm]

#print axioms classRow_vertexCrossKernel
#print axioms classRow_vertexInternalKernel
#print axioms repeatedVertexWeight_load
#print axioms repeatedVertexWeight_rows
#print axioms singletonVertexWeight_load
#print axioms singletonVertexWeight_rows
#print axioms tripartiteVertexWeight_load
#print axioms tripartiteVertexWeight_rows
#print axioms repeatedVertexWeight_bound
#print axioms singletonVertexWeight_bound
#print axioms tripartiteVertexWeight_bound
#print axioms vertexMode_bounds

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
