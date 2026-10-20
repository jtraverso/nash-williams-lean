/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.RealTypeTotals
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.PhysicalTypeModes

@[expose] public section

/-! # The bounded physical correction of all global type totals -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

def EdgeSupported (p : V → Fin 4) (F : Finset (Multiset (Fin 4))) (g : V → V → ℝ) : Prop :=
  ∀ a b, (¬ ∃ k, Link F (p a) (p b) k) → g a b = 0

def F1RealCompatible (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  classTotal p g 0 2 + classTotal p g 0 3 + classTotal p g 1 2 + classTotal p g 1 3 =
    2 * (classTotal p g 0 0 / 2 + classTotal p g 1 1 / 2 +
      classTotal p g 2 2 / 2 + classTotal p g 3 3 / 2)

def F2RealCompatible (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  classTotal p g 0 2 + classTotal p g 0 3 + classTotal p g 1 2 + classTotal p g 1 3 =
    2 * (classTotal p g 0 0 / 2 + classTotal p g 1 1 / 2 + classTotal p g 2 3)

def f1RealMatrix (d0 d1 d2 d3 x02 x03 x12 x13 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![2 * d0, 0, x02, x03], ![0, 2 * d1, x12, x13],
    ![x02, x12, 2 * d2, 0], ![x03, x13, 0, 2 * d3]]

def f2RealMatrix (d0 d1 x02 x03 x12 x13 x23 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![2 * d0, 0, x02, x03], ![0, 2 * d1, x12, x13],
    ![x02, x12, 0, x23], ![x03, x13, x23, 0]]

theorem classTotal_zero_of_inactive (p : V → Fin 4) (F : Finset (Multiset (Fin 4)))
    (g : V → V → ℝ) (hs : EdgeSupported p F g) (i j : Fin 4)
    (hij : ¬ ∃ k, Link F i j k) : classTotal p g i j = 0 := by
  unfold classTotal classRow
  apply sum_eq_zero
  intro a ha
  apply sum_eq_zero
  intro b hb
  apply hs a b
  simpa only [(mem_classVertices p i a).mp ha, (mem_classVertices p j b).mp hb] using hij

theorem classTotal_f1RealMatrix (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p F1 g) :
    classTotal p g = f1RealMatrix (classTotal p g 0 0 / 2) (classTotal p g 1 1 / 2)
      (classTotal p g 2 2 / 2) (classTotal p g 3 3 / 2)
      (classTotal p g 0 2) (classTotal p g 0 3) (classTotal p g 1 2) (classTotal p g 1 3) := by
  have h01 := classTotal_zero_of_inactive p F1 g hs 0 1 (by unfold Link; decide)
  have h23 := classTotal_zero_of_inactive p F1 g hs 2 3 (by unfold Link; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [f1RealMatrix, classTotal_symmetric p g hsym 1 0,
      classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 3 1,
      classTotal_symmetric p g hsym 3 2, h01, h23] <;> ring

theorem classTotal_f2RealMatrix (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p F2 g) :
    classTotal p g = f2RealMatrix (classTotal p g 0 0 / 2) (classTotal p g 1 1 / 2)
      (classTotal p g 0 2) (classTotal p g 0 3) (classTotal p g 1 2) (classTotal p g 1 3)
      (classTotal p g 2 3) := by
  have h01 := classTotal_zero_of_inactive p F2 g hs 0 1 (by unfold Link; decide)
  have h22 := classTotal_zero_of_inactive p F2 g hs 2 2 (by unfold Link; decide)
  have h33 := classTotal_zero_of_inactive p F2 g hs 3 3 (by unfold Link; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [f2RealMatrix, classTotal_symmetric p g hsym 1 0,
      classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 3 1,
      classTotal_symmetric p g hsym 3 2, h01, h22, h33] <;> ring

def f1TypeWeight (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 z6 z7 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 2 z0 a b c + repeatedTypeWeight p 0 3 z1 a b c +
  repeatedTypeWeight p 1 2 z2 a b c + repeatedTypeWeight p 1 3 z3 a b c +
  repeatedTypeWeight p 2 0 z4 a b c + repeatedTypeWeight p 2 1 z5 a b c +
  repeatedTypeWeight p 3 0 z6 a b c + repeatedTypeWeight p 3 1 z7 a b c

def f2TypeWeight (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 : ℝ) (a b c : V) : ℝ :=
  repeatedTypeWeight p 0 2 z0 a b c + repeatedTypeWeight p 0 3 z1 a b c +
  repeatedTypeWeight p 1 2 z2 a b c + repeatedTypeWeight p 1 3 z3 a b c +
  tripartiteTypeWeight p 0 2 3 z4 a b c + tripartiteTypeWeight p 1 2 3 z5 a b c

theorem f1TypeWeight_symmetric (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 z6 z7 : ℝ) :
    TernarySymmetric (f1TypeWeight p z0 z1 z2 z3 z4 z5 z6 z7) := by
  unfold f1TypeWeight
  repeat' first
    | exact repeatedTypeWeight_symmetric p _ _ _
    | apply TernarySymmetric.add

theorem f2TypeWeight_symmetric (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 : ℝ) :
    TernarySymmetric (f2TypeWeight p z0 z1 z2 z3 z4 z5) := by
  unfold f2TypeWeight
  repeat' first
    | exact repeatedTypeWeight_symmetric p _ _ _
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem f1TypeWeight_supported (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 z6 z7 : ℝ) :
    TernarySupported p F1 (f1TypeWeight p z0 z1 z2 z3 z4 z5 z6 z7) := by
  unfold f1TypeWeight
  repeat' first
    | exact aabLift_supported p F1 _ _ (by decide) (by unfold Link; decide) _
    | apply TernarySupported.add

theorem f2TypeWeight_supported (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 : ℝ) :
    TernarySupported p F2 (f2TypeWeight p z0 z1 z2 z3 z4 z5) := by
  unfold f2TypeWeight
  repeat' first
    | exact aabLift_supported p F2 _ _ (by decide) (by unfold Link; decide) _
    | exact abcLift_supported p F2 _ _ _ (by decide) (by decide) (by decide) (by unfold Link; decide) _
    | apply TernarySupported.add

theorem f1TypeWeight_totals (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 z6 z7 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0) :
    classTotal p (ternaryLoad (f1TypeWeight p z0 z1 z2 z3 z4 z5 z6 z7)) =
      f1RealMatrix (z0 + z1) (z2 + z3) (z4 + z5) (z6 + z7)
        (2 * (z0 + z4)) (2 * (z1 + z6)) (2 * (z2 + z5)) (2 * (z3 + z7)) := by
  funext i j
  unfold f1TypeWeight
  simp only [classTotal_ternary_add]
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  simp only [ht]
  fin_cases i <;> fin_cases j <;> simp [f1RealMatrix] <;> ring

theorem f2TypeWeight_totals (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) (hm1 : ∀ i, classSize p i - 1 ≠ 0) :
    classTotal p (ternaryLoad (f2TypeWeight p z0 z1 z2 z3 z4 z5)) =
      f2RealMatrix (z0 + z1) (z2 + z3) (2 * z0 + z4) (2 * z1 + z4)
        (2 * z2 + z5) (2 * z3 + z5) (z4 + z5) := by
  funext i j
  unfold f2TypeWeight
  simp only [classTotal_ternary_add]
  have ht := fun a b z => repeatedTypeWeight_totals p a b z (hm a) (hm1 a) (hm b) i j
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [ht, hu]
  fin_cases i <;> fin_cases j <;> simp [f2RealMatrix] <;> ring

theorem f1TypeWeight_bound (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 z6 z7 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ)
    (hz : ∀ z ∈ [z0, z1, z2, z3, z4, z5, z6, z7], |z| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f1TypeWeight p z0 z1 z2 z3 z4 z5 z6 z7 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := f1TypeWeight_supported p z0 z1 z2 z3 z4 z5 z6 z7
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p F1 a b c := by
      intro h
      rcases hdiag with hdiag | hdiag | hdiag
      · exact h.1 hdiag
      · exact h.2.1 hdiag
      · exact h.2.2.1 hdiag
    rw [hsup a b c hbad, abs_zero]
    exact hM
  have hab : a ≠ b := fun h => hdiag (Or.inl h)
  have hac : a ≠ c := fun h => hdiag (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hdiag (Or.inr (Or.inr h))
  have h0 := repeatedType_normalizer_bound p 0 2 z0 E δ hE hδ (hz z0 (by simp)) hm
  have h1 := repeatedType_normalizer_bound p 0 3 z1 E δ hE hδ (hz z1 (by simp)) hm
  have h2 := repeatedType_normalizer_bound p 1 2 z2 E δ hE hδ (hz z2 (by simp)) hm
  have h3 := repeatedType_normalizer_bound p 1 3 z3 E δ hE hδ (hz z3 (by simp)) hm
  have h4 := repeatedType_normalizer_bound p 2 0 z4 E δ hE hδ (hz z4 (by simp)) hm
  have h5 := repeatedType_normalizer_bound p 2 1 z5 E δ hE hδ (hz z5 (by simp)) hm
  have h6 := repeatedType_normalizer_bound p 3 0 z6 E δ hE hδ (hz z6 (by simp)) hm
  have h7 := repeatedType_normalizer_bound p 3 1 z7 E δ hE hδ (hz z7 (by simp)) hm
  dsimp only [f1TypeWeight, repeatedTypeWeight, aabLift, pairSymmetrize, aabBase]
  generalize ha : p a = i
  generalize hb : p b = j
  generalize hc : p c = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hab, hac, hbc]
  all_goals first
    | exact h0
    | exact h1
    | exact h2
    | exact h3
    | exact h4
    | exact h5
    | exact h6
    | exact h7
    | exact hM

theorem f2TypeWeight_bound (p : V → Fin 4) (z0 z1 z2 z3 z4 z5 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ)
    (hz : ∀ z ∈ [z0, z1, z2, z3, z4, z5], |z| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f2TypeWeight p z0 z1 z2 z3 z4 z5 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := f2TypeWeight_supported p z0 z1 z2 z3 z4 z5
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p F2 a b c := by
      intro h
      rcases hdiag with hdiag | hdiag | hdiag
      · exact h.1 hdiag
      · exact h.2.1 hdiag
      · exact h.2.2.1 hdiag
    rw [hsup a b c hbad, abs_zero]
    exact hM
  have hab : a ≠ b := fun h => hdiag (Or.inl h)
  have hac : a ≠ c := fun h => hdiag (Or.inr (Or.inl h))
  have hbc : b ≠ c := fun h => hdiag (Or.inr (Or.inr h))
  have h0 := repeatedType_normalizer_bound p 0 2 z0 E δ hE hδ (hz z0 (by simp)) hm
  have h1 := repeatedType_normalizer_bound p 0 3 z1 E δ hE hδ (hz z1 (by simp)) hm
  have h2 := repeatedType_normalizer_bound p 1 2 z2 E δ hE hδ (hz z2 (by simp)) hm
  have h3 := repeatedType_normalizer_bound p 1 3 z3 E δ hE hδ (hz z3 (by simp)) hm
  have h4 := tripartiteType_normalizer_bound p 0 2 3 z4 E δ hE hδ (hz z4 (by simp)) hm
  have h5 := tripartiteType_normalizer_bound p 1 2 3 z5 E δ hE hδ (hz z5 (by simp)) hm
  dsimp only [f2TypeWeight, repeatedTypeWeight, tripartiteTypeWeight, aabLift,
    abcLift, pairSymmetrize, aabBase, abcBase]
  generalize ha : p a = i
  generalize hb : p b = j
  generalize hc : p c = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [hab, hac, hbc]
  all_goals first
    | exact h0
    | exact h1
    | exact h2
    | exact h3
    | exact h4
    | exact h5
    | exact hM

theorem exists_type_correction_F1 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p F1 g)
    (hcompat : F1RealCompatible p g) (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p F1 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have hhalf (i : Fin 4) : |classTotal p g i i / 2| ≤ E := by
    apply (uniform_bound _ E 2 (hbound i i) (by norm_num)).trans
    linarith
  have hb : ∀ z ∈ [classTotal p g 0 0 / 2, classTotal p g 1 1 / 2,
      classTotal p g 2 2 / 2, classTotal p g 3 3 / 2, classTotal p g 0 2,
      classTotal p g 0 3, classTotal p g 1 2, classTotal p g 1 3], |z| ≤ E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hhalf _ | exact hbound _ _
  obtain ⟨z0, z1, z2, z3, z4, z5, z6, z7, he, hz⟩ :=
    PaddedF12.RealTypeTotals.f1_solve _ _ _ _ _ _ _ _ E hcompat hb
  obtain ⟨he0, he1, he2, he3, he02, he03, he12, he13⟩ := he
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  refine ⟨f1TypeWeight p z0 z1 z2 z3 z4 z5 z6 z7,
    f1TypeWeight_symmetric p _ _ _ _ _ _ _ _, f1TypeWeight_supported p _ _ _ _ _ _ _ _, ?_, ?_⟩
  · rw [f1TypeWeight_totals p _ _ _ _ _ _ _ _ hn hn1,
      classTotal_f1RealMatrix p g hsym hs, he0, he1, he2, he3, he02, he03, he12, he13]
  · exact f1TypeWeight_bound p _ _ _ _ _ _ _ _ E δ hE hδ hz hm

theorem exists_type_correction_F2 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p F2 g)
    (hcompat : F2RealCompatible p g) (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p F2 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  have hhalf (i : Fin 4) : |classTotal p g i i / 2| ≤ E := by
    apply (uniform_bound _ E 2 (hbound i i) (by norm_num)).trans
    linarith
  have hb : ∀ z ∈ [classTotal p g 0 0 / 2, classTotal p g 1 1 / 2,
      classTotal p g 0 2, classTotal p g 0 3, classTotal p g 1 2,
      classTotal p g 1 3, classTotal p g 2 3], |z| ≤ E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact hhalf _ | exact hbound _ _
  obtain ⟨z0, z1, z2, z3, z4, z5, he, hz⟩ :=
    PaddedF12.RealTypeTotals.f2_solve _ _ _ _ _ _ _ E hcompat hb
  obtain ⟨he0, he1, he02, he03, he12, he13, he23⟩ := he
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  have hn1 (i : Fin 4) : classSize p i - 1 ≠ 0 := by have := hm i; linarith
  refine ⟨f2TypeWeight p z0 z1 z2 z3 z4 z5,
    f2TypeWeight_symmetric p _ _ _ _ _ _, f2TypeWeight_supported p _ _ _ _ _ _, ?_, ?_⟩
  · rw [f2TypeWeight_totals p _ _ _ _ _ _ hn hn1,
      classTotal_f2RealMatrix p g hsym hs, he0, he1, he02, he03, he12, he13, he23]
  · exact f2TypeWeight_bound p _ _ _ _ _ _ E δ hE hδ hz hm

theorem F1RealCompatible.of_span (p : V → Fin 4) (g : V → V → ℝ)
    (hspan : ∃ c : Multiset (Fin 4) → ℝ,
      classTotal p g = ∑ τ ∈ F1, c τ • (fun i j => (typeEdgeVec τ i j : ℝ))) :
    F1RealCompatible p g := PaddedF12.RealTypeTotals.f1_span_free_charge _ hspan

theorem F2RealCompatible.of_span (p : V → Fin 4) (g : V → V → ℝ)
    (hspan : ∃ c : Multiset (Fin 4) → ℝ,
      classTotal p g = ∑ τ ∈ F2, c τ • (fun i j => (typeEdgeVec τ i j : ℝ))) :
    F2RealCompatible p g := PaddedF12.RealTypeTotals.f2_span_free_charge _ hspan

#print axioms f1TypeWeight_totals
#print axioms f2TypeWeight_totals
#print axioms f1TypeWeight_supported
#print axioms f2TypeWeight_supported
#print axioms f1TypeWeight_bound
#print axioms f2TypeWeight_bound
#print axioms exists_type_correction_F1
#print axioms exists_type_correction_F2
#print axioms F1RealCompatible.of_span
#print axioms F2RealCompatible.of_span

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
