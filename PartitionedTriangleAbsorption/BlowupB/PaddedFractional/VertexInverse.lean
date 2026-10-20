/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalVertexModes

/-! # Solving every vertex-to-class row with the F₁ and F₂ links -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

def VertexDemandZero (p : V → Fin 4) (d : V → Fin 4 → ℝ) : Prop :=
  ∀ i j, ∑ a ∈ classVertices p i, d a j = 0

def VertexDemandSupported (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (d : V → Fin 4 → ℝ) : Prop :=
  ∀ a j, (¬ ∃ k, Link F (p a) j k) → d a j = 0

def f1VertexAt (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) (a b c : V) : ℝ :=
  repeatedVertexWeight p i (first1 i) (fun v => d v i) a b c +
  singletonVertexWeight p (first1 i) i (fun v => (d v (first1 i) - d v i) / 2) a b c +
  singletonVertexWeight p (second1 i) i (fun v => d v (second1 i) / 2) a b c

def f1VertexWeight (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  ∑ i : Fin 4, f1VertexAt p d i a b c

theorem f1VertexAt_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) :
    TernarySymmetric (f1VertexAt p d i) := by
  unfold f1VertexAt
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem f1VertexAt_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) :
    TernarySupported p F1 (f1VertexAt p d i) := by
  fin_cases i <;> unfold f1VertexAt <;>
    repeat' first
      | exact aabLift_supported p F1 _ _ (by decide) (by unfold Link; decide) _
      | apply TernarySupported.add

theorem f1VertexWeight_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (f1VertexWeight p d) := TernarySymmetric.sum _ (f1VertexAt_symmetric p d)

theorem f1VertexWeight_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p F1 (f1VertexWeight p d) := TernarySupported.sum p F1 _ (f1VertexAt_supported p d)

theorem f1VertexAt_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p F1 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (f1VertexAt p d i)) a k = if p a = i then d a k else 0 := by
  have hc : (∑ v ∈ classVertices p i, (d v (first1 i) - d v i) / 2) = 0 := by
    rw [← sum_div, sum_sub_distrib, hz i (first1 i), hz i i, sub_self, zero_div]
  have hd : (∑ v ∈ classVertices p i, d v (second1 i) / 2) = 0 := by
    rw [← sum_div, hz i (second1 i), zero_div]
  unfold f1VertexAt
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p i (first1 i) (fun v => d v i) (hz i i) (hm2 i) (hm (first1 i)),
    singletonVertexWeight_rows p (first1 i) i _ hc (hm (first1 i)) (hm1 (first1 i)),
    singletonVertexWeight_rows p (second1 i) i _ hd (hm (second1 i)) (hm1 (second1 i))]
  by_cases ha : p a = i
  · have hforb := hs a k
    rw [ha] at hforb
    fin_cases i <;> fin_cases k <;> simp [first1, second1, ha]
    all_goals first
      | exact (hforb (by unfold Link; decide)).symm
      | ring
  · simp [ha]

theorem f1VertexWeight_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p F1 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (f1VertexWeight p d)) a k = d a k := by
  unfold f1VertexWeight
  rw [classRow_ternary_sum]
  simp_rw [f1VertexAt_rows p d _ hz hs hm hm1 hm2 a k]
  simp

theorem abs_three_bound {x y z M : ℝ} (hx : |x| ≤ M) (hy : |y| ≤ M) (hz : |z| ≤ M) :
    |x + y + z| ≤ 3 * M := by
  rw [abs_le] at hx hy hz ⊢
  constructor <;> linarith

theorem f1VertexAt_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f1VertexAt p d i a b c| ≤ 72 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hc0 (v : V) : |d v i| ≤ 2 * D := by have := hd v i; linarith
  have hc1 (v : V) : |(d v (first1 i) - d v i) / 2| ≤ 2 * D := by
    have h := (star_loop_link_bound _ _ _ D (hd v i) (hd v (first1 i)) (hd v (second1 i))).2.2.1
    linarith
  have hc2 (v : V) : |d v (second1 i) / 2| ≤ 2 * D := by
    have h := (star_loop_link_bound _ _ _ D (hd v i) (hd v (first1 i)) (hd v (second1 i))).2.2.2
    linarith
  have h0 := (vertexMode_bounds p (fun v => d v i) (2 * D) δ h2D hδ hc0 hm a b c).1 i (first1 i)
  have h1 := (vertexMode_bounds p (fun v => (d v (first1 i) - d v i) / 2)
    (2 * D) δ h2D hδ hc1 hm a b c).2.1 (first1 i) i
  have h2 := (vertexMode_bounds p (fun v => d v (second1 i) / 2)
    (2 * D) δ h2D hδ hc2 hm a b c).2.1 (second1 i) i
  calc
    _ ≤ 3 * (12 * (2 * D) / δ ^ 2) := abs_three_bound h0 h1 h2
    _ = 72 * D / δ ^ 2 := by ring

theorem f1VertexWeight_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f1VertexWeight p d a b c| ≤ 288 * D / δ ^ 2 := by
  calc
    _ ≤ ∑ i : Fin 4, |f1VertexAt p d i a b c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, 72 * D / δ ^ 2 :=
      sum_le_sum (fun i _ => f1VertexAt_bound p d i D δ hD hδ hd hm a b c)
    _ = 288 * D / δ ^ 2 := by simp; ring

def f2LowerVertexAt (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) (a b c : V) : ℝ :=
  repeatedVertexWeight p (lower2 i) 2
    (fun v => (d v (lower2 i) + d v 2 - d v 3) / 2) a b c +
  repeatedVertexWeight p (lower2 i) 3
    (fun v => (d v (lower2 i) + d v 3 - d v 2) / 2) a b c +
  tripartiteVertexWeight p (lower2 i) 2 3
    (fun v => (d v 2 + d v 3 - d v (lower2 i)) / 2) a b c

def f2UpperVertexAt (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) (a b c : V) : ℝ :=
  tripartiteVertexWeight p (upper2 i) (central2 i) 0 (fun v => d v (central2 i)) a b c +
  singletonVertexWeight p 0 (upper2 i) (fun v => (d v 0 - d v (central2 i)) / 2) a b c +
  singletonVertexWeight p 1 (upper2 i) (fun v => d v 1 / 2) a b c

def f2VertexWeight (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  (∑ i : Fin 2, f2LowerVertexAt p d i a b c) + (∑ i : Fin 2, f2UpperVertexAt p d i a b c)

theorem f2LowerVertexAt_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) :
    TernarySymmetric (f2LowerVertexAt p d i) := by
  unfold f2LowerVertexAt
  repeat' first
    | exact repeatedVertexWeight_symmetric p _ _ _
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem f2UpperVertexAt_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) :
    TernarySymmetric (f2UpperVertexAt p d i) := by
  unfold f2UpperVertexAt
  repeat' first
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | exact singletonVertexWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem f2LowerVertexAt_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) :
    TernarySupported p F2 (f2LowerVertexAt p d i) := by
  fin_cases i <;> unfold f2LowerVertexAt <;>
    repeat' first
      | exact aabLift_supported p F2 _ _ (by decide) (by unfold Link; decide) _
      | exact abcLift_supported p F2 _ _ _ (by decide) (by decide) (by decide) (by unfold Link; decide) _
      | apply TernarySupported.add

theorem f2UpperVertexAt_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) :
    TernarySupported p F2 (f2UpperVertexAt p d i) := by
  fin_cases i <;> unfold f2UpperVertexAt <;>
    repeat' first
      | exact aabLift_supported p F2 _ _ (by decide) (by unfold Link; decide) _
      | exact abcLift_supported p F2 _ _ _ (by decide) (by decide) (by decide) (by unfold Link; decide) _
      | apply TernarySupported.add

theorem f2VertexWeight_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (f2VertexWeight p d) :=
  (TernarySymmetric.sum _ (f2LowerVertexAt_symmetric p d)).add
    (TernarySymmetric.sum _ (f2UpperVertexAt_symmetric p d))

theorem f2VertexWeight_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p F2 (f2VertexWeight p d) :=
  (TernarySupported.sum p F2 _ (f2LowerVertexAt_supported p d)).add
    (TernarySupported.sum p F2 _ (f2UpperVertexAt_supported p d))

theorem f2LowerVertexAt_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p F2 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (f2LowerVertexAt p d i)) a k = if p a = lower2 i then d a k else 0 := by
  unfold VertexDemandZero at hz
  have h0 : (∑ v ∈ classVertices p (lower2 i), (d v (lower2 i) + d v 2 - d v 3) / 2) = 0 := by
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  have h1 : (∑ v ∈ classVertices p (lower2 i), (d v (lower2 i) + d v 3 - d v 2) / 2) = 0 := by
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  have h2 : (∑ v ∈ classVertices p (lower2 i), (d v 2 + d v 3 - d v (lower2 i)) / 2) = 0 := by
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  unfold f2LowerVertexAt
  simp only [classRow_ternary_add]
  rw [repeatedVertexWeight_rows p (lower2 i) 2 _ h0 (hm2 (lower2 i)) (hm 2),
    repeatedVertexWeight_rows p (lower2 i) 3 _ h1 (hm2 (lower2 i)) (hm 3),
    tripartiteVertexWeight_rows p (lower2 i) 2 3 _ h2 (hm 2) (hm 3)]
  by_cases ha : p a = lower2 i
  · have hforb := hs a k
    rw [ha] at hforb
    fin_cases i <;> fin_cases k <;> simp [ha, lower2]
    all_goals first
      | exact (hforb (by unfold Link; decide)).symm
      | ring
  · simp [ha]

theorem f2UpperVertexAt_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p F2 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (f2UpperVertexAt p d i)) a k = if p a = upper2 i then d a k else 0 := by
  unfold VertexDemandZero at hz
  have h1 : (∑ v ∈ classVertices p (upper2 i), (d v 0 - d v (central2 i)) / 2) = 0 := by
    simp only [← sum_div, sum_sub_distrib, hz, sub_self, zero_div]
  have h2 : (∑ v ∈ classVertices p (upper2 i), d v 1 / 2) = 0 := by
    rw [← sum_div, hz, zero_div]
  unfold f2UpperVertexAt
  simp only [classRow_ternary_add]
  rw [tripartiteVertexWeight_rows p (upper2 i) (central2 i) 0 _
      (hz (upper2 i) (central2 i)) (hm (central2 i)) (hm 0),
    singletonVertexWeight_rows p 0 (upper2 i) _ h1 (hm 0) (hm1 0),
    singletonVertexWeight_rows p 1 (upper2 i) _ h2 (hm 1) (hm1 1)]
  by_cases ha : p a = upper2 i
  · have hforb := hs a k
    rw [ha] at hforb
    fin_cases i <;> fin_cases k <;> simp [ha, upper2, central2]
    all_goals first
      | exact (hforb (by unfold Link; decide)).symm
      | ring
  · simp [ha]

theorem f2VertexWeight_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p F2 d)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0)
    (hm2 : ∀ i, classSize p i - 2 ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (f2VertexWeight p d)) a k = d a k := by
  unfold f2VertexWeight
  rw [classRow_ternary_add, classRow_ternary_sum, classRow_ternary_sum]
  simp_rw [f2LowerVertexAt_rows p d _ hz hs hm hm2 a k,
    f2UpperVertexAt_rows p d _ hz hs hm hm1 a k]
  generalize ha : p a = i
  fin_cases i <;> simp [lower2, upper2, Fin.sum_univ_succ]

theorem f2LowerVertexAt_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f2LowerVertexAt p d i a b c| ≤ 72 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hc (v : V) := triangle_link_bound _ _ _ D (hd v (lower2 i)) (hd v 2) (hd v 3)
  have h0 := (vertexMode_bounds p (fun v => (d v (lower2 i) + d v 2 - d v 3) / 2)
    (2 * D) δ h2D hδ (fun v => (hc v).1) hm a b c).1 (lower2 i) 2
  have h1 := (vertexMode_bounds p (fun v => (d v (lower2 i) + d v 3 - d v 2) / 2)
    (2 * D) δ h2D hδ (fun v => (hc v).2.1) hm a b c).1 (lower2 i) 3
  have h2 := (vertexMode_bounds p (fun v => (d v 2 + d v 3 - d v (lower2 i)) / 2)
    (2 * D) δ h2D hδ (fun v => (hc v).2.2) hm a b c).2.2 (lower2 i) 2 3
  calc
    _ ≤ 3 * (12 * (2 * D) / δ ^ 2) := abs_three_bound h0 h1 h2
    _ = 72 * D / δ ^ 2 := by ring

theorem f2UpperVertexAt_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 2) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f2UpperVertexAt p d i a b c| ≤ 72 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hc0 (v : V) : |d v (central2 i)| ≤ 2 * D := by have := hd v (central2 i); linarith
  have hc1 (v : V) : |(d v 0 - d v (central2 i)) / 2| ≤ 2 * D := by
    have h := (star_loop_link_bound _ _ _ D (hd v (central2 i)) (hd v 0) (hd v 1)).2.2.1
    linarith
  have hc2 (v : V) : |d v 1 / 2| ≤ 2 * D := by
    have h := (star_loop_link_bound _ _ _ D (hd v (central2 i)) (hd v 0) (hd v 1)).2.2.2
    linarith
  have h0 := (vertexMode_bounds p (fun v => d v (central2 i))
    (2 * D) δ h2D hδ hc0 hm a b c).2.2 (upper2 i) (central2 i) 0
  have h1 := (vertexMode_bounds p (fun v => (d v 0 - d v (central2 i)) / 2)
    (2 * D) δ h2D hδ hc1 hm a b c).2.1 0 (upper2 i)
  have h2 := (vertexMode_bounds p (fun v => d v 1 / 2)
    (2 * D) δ h2D hδ hc2 hm a b c).2.1 1 (upper2 i)
  calc
    _ ≤ 3 * (12 * (2 * D) / δ ^ 2) := abs_three_bound h0 h1 h2
    _ = 72 * D / δ ^ 2 := by ring

theorem f2VertexWeight_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f2VertexWeight p d a b c| ≤ 288 * D / δ ^ 2 := by
  have hl : |∑ i : Fin 2, f2LowerVertexAt p d i a b c| ≤ 144 * D / δ ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 2, |f2LowerVertexAt p d i a b c| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 2, 72 * D / δ ^ 2 :=
        sum_le_sum (fun i _ => f2LowerVertexAt_bound p d i D δ hD hδ hd hm a b c)
      _ = 144 * D / δ ^ 2 := by simp; ring
  have hu : |∑ i : Fin 2, f2UpperVertexAt p d i a b c| ≤ 144 * D / δ ^ 2 := by
    calc
      _ ≤ ∑ i : Fin 2, |f2UpperVertexAt p d i a b c| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 2, 72 * D / δ ^ 2 :=
        sum_le_sum (fun i _ => f2UpperVertexAt_bound p d i D δ hD hδ hd hm a b c)
      _ = 144 * D / δ ^ 2 := by simp; ring
  calc
    _ ≤ |∑ i : Fin 2, f2LowerVertexAt p d i a b c| +
        |∑ i : Fin 2, f2UpperVertexAt p d i a b c| := abs_add_le _ _
    _ ≤ 144 * D / δ ^ 2 + 144 * D / δ ^ 2 := add_le_add hl hu
    _ = 288 * D / δ ^ 2 := by ring

#print axioms f1VertexWeight_symmetric
#print axioms f1VertexWeight_supported
#print axioms f1VertexWeight_rows
#print axioms f1VertexWeight_bound
#print axioms f2VertexWeight_symmetric
#print axioms f2VertexWeight_supported
#print axioms f2VertexWeight_rows
#print axioms f2VertexWeight_bound

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
