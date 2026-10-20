/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.HostInverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.LoadDefect
public import PartitionedTriangleAbsorption.BlowupB.PaddedF3.Universal

@[expose] public section

/-!
# The bounded signed inverse for F₃

F₃ = {012, 013, 023, 123}: every allowed pair joins two distinct classes and
every type is tripartite. The three stages of the F₁/F₂ inverse become:

* totals: `z₀₁₂ = (x₀₁ + x₀₂ - x₀₃)/2`, `z₀₁₃ = (x₀₁ + x₀₃ - x₀₂)/2`,
  `z₀₂₃ = (x₀₂ + x₀₃ - x₀₁)/2`, `z₁₂₃ = x₁₂ - z₀₁₂`, using the two real
  compatibility relations `x₀₁ + x₂₃ = x₀₂ + x₁₃ = x₀₃ + x₁₂`;
* vertex rows: for `v ∈ V_i` with other classes `j, k, l`, three tripartite
  modes with demands `(d_j + d_k - d_l)/2` and its permutations;
* zero rows: one tripartite edge mode for each of the six class pairs.

The bound `2^20 ε / (γ^6 n)` of the F₁/F₂ inverse is kept, so the host transfer and
the repair budgets are unchanged.
-/

noncomputable section

namespace PaddedF3

open Finset PartitionedTriangleAbsorption
open PartitionedTriangleAbsorption.TypedTransformer
open PartitionedTriangleAbsorption.TypedApplicationLinks
open PartitionedTriangleAbsorption.StructuralF3General
open PartitionedTriangleAbsorption.BlowupB.PaddedFractional
open PartitionedTriangleAbsorption.BlowupB.PaddedNibble.TypedNibble

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

/-! ### Real compatibility -/

def F3RealCompatible (p : V → Fin 4) (g : V → V → ℝ) : Prop :=
  classTotal p g 0 1 + classTotal p g 2 3 = classTotal p g 0 2 + classTotal p g 1 3 ∧
  classTotal p g 0 2 + classTotal p g 1 3 = classTotal p g 0 3 + classTotal p g 1 2

theorem f3_span_compat (A : Fin 4 → Fin 4 → ℝ)
    (hspan : ∃ c : Multiset (Fin 4) → ℝ,
      A = ∑ τ ∈ F3, c τ • (fun i j => (typeEdgeVec τ i j : ℝ))) :
    A 0 1 + A 2 3 = A 0 2 + A 1 3 ∧ A 0 2 + A 1 3 = A 0 3 + A 1 2 := by
  obtain ⟨c, rfl⟩ := hspan
  rw [sum_F3]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    tev01.1, tev01.2.1, tev01.2.2.1, tev01.2.2.2, tev02.1, tev02.2.1, tev02.2.2.1, tev02.2.2.2,
    tev03.1, tev03.2.1, tev03.2.2.1, tev03.2.2.2, tev12.1, tev12.2.1, tev12.2.2.1, tev12.2.2.2,
    tev13.1, tev13.2.1, tev13.2.2.1, tev13.2.2.2, tev23.1, tev23.2.1, tev23.2.2.1, tev23.2.2.2,
    Int.cast_one, Int.cast_zero]
  constructor <;> ring

theorem F3RealCompatible.of_span (p : V → Fin 4) (g : V → V → ℝ)
    (hspan : ∃ c : Multiset (Fin 4) → ℝ,
      classTotal p g = ∑ τ ∈ F3, c τ • (fun i j => (typeEdgeVec τ i j : ℝ))) :
    F3RealCompatible p g := f3_span_compat _ hspan

theorem F3RealCompatible.sub {p : V → Fin 4} {g h : V → V → ℝ}
    (hg : F3RealCompatible p g) (hh : F3RealCompatible p h) :
    F3RealCompatible p (fun a b => g a b - h a b) := by
  unfold F3RealCompatible at *
  simp only [classTotal_sub]
  constructor <;> linarith [hg.1, hg.2, hh.1, hh.2]

theorem F3RealCompatible.indicator_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F3 E) :
    F3RealCompatible p (fun a b => edgeIndicator E s(a, b)) := by
  apply F3RealCompatible.of_span
  rw [classTotal_edgeIndicator p E hloop]
  exact PaddedF12.RealTypeTotals.real_span_of_isIntDiv p F3 E hdiv

theorem F3RealCompatible.of_boundary (p : V → Fin 4) (G : SimpleGraph V)
    (z : TriangleChain V) (hz : CopySupported p F3 G z) :
    F3RealCompatible p (fun a b => boundary z s(a, b)) :=
  F3RealCompatible.of_span p _ (real_span_boundary p F3 G z hz)

theorem F3RealCompatible.residual_of_isIntDiv (p : V → Fin 4) (E : Finset (Sym2 V))
    (hloop : ∀ e ∈ E, ¬ e.IsDiag) (hdiv : IsIntDiv p F3 E) (G : SimpleGraph V)
    (z : TriangleChain V) (hz : CopySupported p F3 G z) :
    F3RealCompatible p (fun a b => edgeIndicator E s(a, b) - boundary z s(a, b)) :=
  (F3RealCompatible.indicator_of_isIntDiv p E hloop hdiv).sub
    (F3RealCompatible.of_boundary p G z hz)

/-! ### Stage 1: class totals -/

def f3Matrix (x01 x02 x03 x12 x13 x23 : ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![0, x01, x02, x03], ![x01, 0, x12, x13],
    ![x02, x12, 0, x23], ![x03, x13, x23, 0]]

theorem classTotal_f3Matrix (p : V → Fin 4) (g : V → V → ℝ)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p F3 g) :
    classTotal p g = f3Matrix (classTotal p g 0 1) (classTotal p g 0 2) (classTotal p g 0 3)
      (classTotal p g 1 2) (classTotal p g 1 3) (classTotal p g 2 3) := by
  have h00 := classTotal_zero_of_inactive p F3 g hs 0 0 (by unfold Link F3; decide)
  have h11 := classTotal_zero_of_inactive p F3 g hs 1 1 (by unfold Link F3; decide)
  have h22 := classTotal_zero_of_inactive p F3 g hs 2 2 (by unfold Link F3; decide)
  have h33 := classTotal_zero_of_inactive p F3 g hs 3 3 (by unfold Link F3; decide)
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [f3Matrix, classTotal_symmetric p g hsym 1 0,
      classTotal_symmetric p g hsym 2 0, classTotal_symmetric p g hsym 2 1,
      classTotal_symmetric p g hsym 3 0, classTotal_symmetric p g hsym 3 1,
      classTotal_symmetric p g hsym 3 2, h00, h11, h22, h33]

def f3TypeWeight (p : V → Fin 4) (z0 z1 z2 z3 : ℝ) (a b c : V) : ℝ :=
  tripartiteTypeWeight p 0 1 2 z0 a b c + tripartiteTypeWeight p 0 1 3 z1 a b c +
  tripartiteTypeWeight p 0 2 3 z2 a b c + tripartiteTypeWeight p 1 2 3 z3 a b c

theorem f3TypeWeight_symmetric (p : V → Fin 4) (z0 z1 z2 z3 : ℝ) :
    TernarySymmetric (f3TypeWeight p z0 z1 z2 z3) := by
  unfold f3TypeWeight
  repeat' first
    | exact tripartiteTypeWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem f3TypeWeight_supported (p : V → Fin 4) (z0 z1 z2 z3 : ℝ) :
    TernarySupported p F3 (f3TypeWeight p z0 z1 z2 z3) := by
  unfold f3TypeWeight
  repeat' first
    | exact abcLift_supported p F3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link F3; decide) _
    | apply TernarySupported.add

theorem f3TypeWeight_totals (p : V → Fin 4) (z0 z1 z2 z3 : ℝ)
    (hm : ∀ i, classSize p i ≠ 0) :
    classTotal p (ternaryLoad (f3TypeWeight p z0 z1 z2 z3)) =
      f3Matrix (z0 + z1) (z0 + z2) (z1 + z2) (z0 + z3) (z1 + z3) (z2 + z3) := by
  funext i j
  unfold f3TypeWeight
  simp only [classTotal_ternary_add]
  have hu := fun a b c z => tripartiteTypeWeight_totals p a b c z (hm a) (hm b) (hm c) i j
  simp only [hu]
  fin_cases i <;> fin_cases j <;> simp [f3Matrix] <;> ring

theorem f3TypeWeight_bound (p : V → Fin 4) (z0 z1 z2 z3 E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ)
    (hz : ∀ z ∈ [z0, z1, z2, z3], |z| ≤ 8 * E)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f3TypeWeight p z0 z1 z2 z3 a b c| ≤ 32 * E / δ ^ 3 := by
  have hM : 0 ≤ 32 * E / δ ^ 3 := by positivity
  have hsup := f3TypeWeight_supported p z0 z1 z2 z3
  by_cases hdiag : a = b ∨ a = c ∨ b = c
  · have hbad : ¬ AdmissibleTriple p F3 a b c := by
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
  have h0 := tripartiteType_normalizer_bound p 0 1 2 z0 E δ hE hδ (hz z0 (by simp)) hm
  have h1 := tripartiteType_normalizer_bound p 0 1 3 z1 E δ hE hδ (hz z1 (by simp)) hm
  have h2 := tripartiteType_normalizer_bound p 0 2 3 z2 E δ hE hδ (hz z2 (by simp)) hm
  have h3 := tripartiteType_normalizer_bound p 1 2 3 z3 E δ hE hδ (hz z3 (by simp)) hm
  dsimp only [f3TypeWeight, tripartiteTypeWeight, abcLift, pairSymmetrize, abcBase]
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
    | exact hM

theorem exists_type_correction_F3 (p : V → Fin 4) (g : V → V → ℝ) (E δ : ℝ)
    (hE : 0 ≤ E) (hδ : 4 ≤ δ) (hm : ∀ i, δ ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hs : EdgeSupported p F3 g)
    (hcompat : F3RealCompatible p g) (hbound : ∀ i j, |classTotal p g i j| ≤ E) :
    ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p F3 w ∧
      classTotal p (ternaryLoad w) = classTotal p g ∧
      ∀ a b c, |w a b c| ≤ 32 * E / δ ^ 3 := by
  obtain ⟨hc1, hc2⟩ := hcompat
  have b01 := abs_le.mp (hbound 0 1)
  have b02 := abs_le.mp (hbound 0 2)
  have b03 := abs_le.mp (hbound 0 3)
  have b12 := abs_le.mp (hbound 1 2)
  let z0 := (classTotal p g 0 1 + classTotal p g 0 2 - classTotal p g 0 3) / 2
  let z1 := (classTotal p g 0 1 + classTotal p g 0 3 - classTotal p g 0 2) / 2
  let z2 := (classTotal p g 0 2 + classTotal p g 0 3 - classTotal p g 0 1) / 2
  let z3 := classTotal p g 1 2 -
    (classTotal p g 0 1 + classTotal p g 0 2 - classTotal p g 0 3) / 2
  have hz : ∀ z ∈ [z0, z1, z2, z3], |z| ≤ 8 * E := by
    intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl <;>
      apply abs_le.mpr <;> constructor <;> dsimp only [z0, z1, z2, z3] <;> linarith
  have hn (i : Fin 4) : classSize p i ≠ 0 := by have := hm i; linarith
  refine ⟨f3TypeWeight p z0 z1 z2 z3, f3TypeWeight_symmetric p _ _ _ _,
    f3TypeWeight_supported p _ _ _ _, ?_, f3TypeWeight_bound p _ _ _ _ E δ hE hδ hz hm⟩
  rw [f3TypeWeight_totals p _ _ _ _ hn, classTotal_f3Matrix p g hsym hs]
  congr 1 <;> dsimp only [z0, z1, z2, z3] <;> linarith

/-! ### Stage 2: vertex rows -/

def oth1 : Fin 4 → Fin 4 := ![1, 0, 0, 0]
def oth2 : Fin 4 → Fin 4 := ![2, 2, 1, 1]
def oth3 : Fin 4 → Fin 4 := ![3, 3, 3, 2]

def f3VertexAt (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) (a b c : V) : ℝ :=
  tripartiteVertexWeight p i (oth1 i) (oth2 i)
    (fun v => (d v (oth1 i) + d v (oth2 i) - d v (oth3 i)) / 2) a b c +
  tripartiteVertexWeight p i (oth1 i) (oth3 i)
    (fun v => (d v (oth1 i) + d v (oth3 i) - d v (oth2 i)) / 2) a b c +
  tripartiteVertexWeight p i (oth2 i) (oth3 i)
    (fun v => (d v (oth2 i) + d v (oth3 i) - d v (oth1 i)) / 2) a b c

def f3VertexWeight (p : V → Fin 4) (d : V → Fin 4 → ℝ) (a b c : V) : ℝ :=
  ∑ i : Fin 4, f3VertexAt p d i a b c

theorem f3VertexAt_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) :
    TernarySymmetric (f3VertexAt p d i) := by
  unfold f3VertexAt
  repeat' first
    | exact tripartiteVertexWeight_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem f3VertexAt_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) :
    TernarySupported p F3 (f3VertexAt p d i) := by
  fin_cases i <;> unfold f3VertexAt <;>
    repeat' first
      | exact abcLift_supported p F3 _ _ _ (by decide) (by decide) (by decide)
          (by unfold Link F3; decide) _
      | apply TernarySupported.add

theorem f3VertexWeight_symmetric (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySymmetric (f3VertexWeight p d) := TernarySymmetric.sum _ (f3VertexAt_symmetric p d)

theorem f3VertexWeight_supported (p : V → Fin 4) (d : V → Fin 4 → ℝ) :
    TernarySupported p F3 (f3VertexWeight p d) :=
  TernarySupported.sum p F3 _ (f3VertexAt_supported p d)

theorem f3VertexAt_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p F3 d)
    (hm : ∀ i, classSize p i ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (f3VertexAt p d i)) a k = if p a = i then d a k else 0 := by
  unfold VertexDemandZero at hz
  have h0 : (∑ v ∈ classVertices p i, (d v (oth1 i) + d v (oth2 i) - d v (oth3 i)) / 2) = 0 := by
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  have h1 : (∑ v ∈ classVertices p i, (d v (oth1 i) + d v (oth3 i) - d v (oth2 i)) / 2) = 0 := by
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  have h2 : (∑ v ∈ classVertices p i, (d v (oth2 i) + d v (oth3 i) - d v (oth1 i)) / 2) = 0 := by
    simp only [← sum_div, sum_sub_distrib, sum_add_distrib, hz, add_zero, sub_self, zero_div]
  unfold f3VertexAt
  simp only [classRow_ternary_add]
  rw [tripartiteVertexWeight_rows p i (oth1 i) (oth2 i) _ h0 (hm _) (hm _),
    tripartiteVertexWeight_rows p i (oth1 i) (oth3 i) _ h1 (hm _) (hm _),
    tripartiteVertexWeight_rows p i (oth2 i) (oth3 i) _ h2 (hm _) (hm _)]
  by_cases ha : p a = i
  · have hforb := hs a k
    rw [ha] at hforb
    fin_cases i <;> fin_cases k <;> simp [ha, oth1, oth2, oth3]
    all_goals first
      | exact (hforb (by unfold Link F3; decide)).symm
      | ring
  · simp [ha]

theorem f3VertexWeight_rows (p : V → Fin 4) (d : V → Fin 4 → ℝ)
    (hz : VertexDemandZero p d) (hs : VertexDemandSupported p F3 d)
    (hm : ∀ i, classSize p i ≠ 0) (a : V) (k : Fin 4) :
    classRow p (ternaryLoad (f3VertexWeight p d)) a k = d a k := by
  unfold f3VertexWeight
  rw [classRow_ternary_sum]
  simp_rw [f3VertexAt_rows p d _ hz hs hm a k]
  simp

theorem f3VertexAt_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (i : Fin 4) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f3VertexAt p d i a b c| ≤ 72 * D / δ ^ 2 := by
  have h2D : 0 ≤ 2 * D := by positivity
  have hc (v : V) := triangle_link_bound _ _ _ D (hd v (oth1 i)) (hd v (oth2 i)) (hd v (oth3 i))
  have h0 := (vertexMode_bounds p (fun v => (d v (oth1 i) + d v (oth2 i) - d v (oth3 i)) / 2)
    (2 * D) δ h2D hδ (fun v => (hc v).1) hm a b c).2.2 i (oth1 i) (oth2 i)
  have h1 := (vertexMode_bounds p (fun v => (d v (oth1 i) + d v (oth3 i) - d v (oth2 i)) / 2)
    (2 * D) δ h2D hδ (fun v => (hc v).2.1) hm a b c).2.2 i (oth1 i) (oth3 i)
  have h2 := (vertexMode_bounds p (fun v => (d v (oth2 i) + d v (oth3 i) - d v (oth1 i)) / 2)
    (2 * D) δ h2D hδ (fun v => (hc v).2.2) hm a b c).2.2 i (oth2 i) (oth3 i)
  calc
    _ ≤ 3 * (12 * (2 * D) / δ ^ 2) := abs_three_bound h0 h1 h2
    _ = 72 * D / δ ^ 2 := by ring

theorem f3VertexWeight_bound (p : V → Fin 4) (d : V → Fin 4 → ℝ) (D δ : ℝ)
    (hD : 0 ≤ D) (hδ : 4 ≤ δ) (hd : ∀ a j, |d a j| ≤ D)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f3VertexWeight p d a b c| ≤ 288 * D / δ ^ 2 := by
  unfold f3VertexWeight
  calc
    _ ≤ ∑ i : Fin 4, |f3VertexAt p d i a b c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, 72 * D / δ ^ 2 :=
      sum_le_sum (fun i _ => f3VertexAt_bound p d i D δ hD hδ hd hm a b c)
    _ = 288 * D / δ ^ 2 := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-! ### Stage 3: zero rows -/

def f3ZeroRowWeight (p : V → Fin 4) (g : V → V → ℝ) (a b c : V) : ℝ :=
  tripartitePairWeight p 0 1 2 g a b c + tripartitePairWeight p 0 2 1 g a b c +
  tripartitePairWeight p 0 3 1 g a b c + tripartitePairWeight p 1 2 0 g a b c +
  tripartitePairWeight p 1 3 0 g a b c + tripartitePairWeight p 2 3 0 g a b c

theorem f3ZeroRowWeight_symmetric (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySymmetric (f3ZeroRowWeight p g) := by
  unfold f3ZeroRowWeight
  repeat' first
    | exact abcLift_symmetric p _ _ _ _
    | apply TernarySymmetric.add

theorem f3ZeroRowWeight_supported (p : V → Fin 4) (g : V → V → ℝ) :
    TernarySupported p F3 (f3ZeroRowWeight p g) := by
  unfold f3ZeroRowWeight
  repeat' first
    | exact abcLift_supported p F3 _ _ _ (by decide) (by decide) (by decide)
        (by unfold Link F3; decide) _
    | apply TernarySupported.add

theorem f3ZeroRowWeight_load (p : V → Fin 4) (g : V → V → ℝ)
    (hs : ∀ a b, g a b = g b a) (hr : ClassRowsZero p g)
    (hsup : ∀ a b, (¬ ∃ k, Link F3 (p a) (p b) k) → g a b = 0)
    (hm : ∀ i, classSize p i ≠ 0) (a b : V) :
    ternaryLoad (f3ZeroRowWeight p g) a b = g a b := by
  have htri := fun i j k a b => tripartitePairWeight_load p i j k g hs hr (hm k) a b
  unfold f3ZeroRowWeight
  simp only [ternaryLoad_add, htri]
  have hf := hsup a b
  generalize ha : p a = i at hf ⊢
  generalize hb : p b = j at hf ⊢
  fin_cases i <;> fin_cases j <;> simp
  all_goals exact (hf (by unfold Link F3; decide)).symm

theorem f3ZeroRowWeight_bound (p : V → Fin 4) (g : V → V → ℝ) (ε δ : ℝ)
    (hε : 0 ≤ ε) (hδ : 4 ≤ δ) (hg : ∀ a b, |g a b| ≤ ε)
    (hm : ∀ i, δ ≤ classSize p i) (a b c : V) :
    |f3ZeroRowWeight p g a b c| ≤ 96 * ε / δ := by
  obtain ⟨_, _, ht⟩ := edgeMode_bounds p g ε δ hε hδ hg hm a b c
  have h0 := ht 0 1 2
  have h1 := ht 0 2 1
  have h2 := ht 0 3 1
  have h3 := ht 1 2 0
  have h4 := ht 1 3 0
  have h5 := ht 2 3 0
  have hpos : 0 ≤ 12 * ε / δ := by
    have : (0 : ℝ) < δ := by linarith
    positivity
  have hM : 96 * ε / δ = 8 * (12 * ε / δ) := by ring
  rw [hM]
  generalize 12 * ε / δ = M at h0 h1 h2 h3 h4 h5 hpos ⊢
  unfold f3ZeroRowWeight
  rw [abs_le] at h0 h1 h2 h3 h4 h5 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2]

/-! ### The complete and host inverses -/

theorem exists_complete_inverse_F3 (p : V → Fin 4) (g : V → V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hsym : ∀ a b, g a b = g b a) (hd : ∀ a, g a a = 0)
    (hs : EdgeSupported p F3 g) (hg : ∀ a b, |g a b| ≤ ε)
    (hc : F3RealCompatible p g) :
    ∃ w : V → V → V → ℝ, TernarySymmetric w ∧ TernarySupported p F3 w ∧
      (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  let n : ℝ := Fintype.card V
  have hn : 0 < n := by
    exact (mul_pos_iff_of_pos_left hγ).mp (lt_of_lt_of_le (by norm_num) hlarge)
  have hn0 : n ≠ 0 := ne_of_gt hn
  have hγ0 : γ ≠ 0 := ne_of_gt hγ
  have hε1 : 0 ≤ 33 * ε / γ ^ 3 := by positivity
  have hε2 : 0 ≤ 9537 * ε / γ ^ 5 := by positivity
  have hm (i : Fin 4) : classSize p i ≠ 0 := by have := hmin i; linarith
  obtain ⟨hstep1, hstep2, hbudget⟩ := complete_inverse_budgets ε γ n hε hγ hγ1 hn
  have he0 : 32 * (ε * n ^ 2) / (γ * n) ^ 3 = 32 * ε / (γ ^ 3 * n) := by
    field_simp [hγ0, hn0]
  have he1 : 288 * (n * (33 * ε / γ ^ 3)) / (γ * n) ^ 2 =
      9504 * ε / (γ ^ 5 * n) := by
    field_simp [hγ0, hn0]
    ring
  have he2 : 96 * (9537 * ε / γ ^ 5) / (γ * n) = 915552 * ε / (γ ^ 6 * n) := by
    field_simp [hγ0, hn0]
    ring
  have hstage : ∃ w : V → V → V → ℝ,
      TernarySymmetric w ∧ TernarySupported p F3 w ∧ (∀ a b, ternaryLoad w a b = g a b) ∧
      ∀ a b c, |w a b c| ≤
        32 * ε / (γ ^ 3 * n) + 9504 * ε / (γ ^ 5 * n) + 915552 * ε / (γ ^ 6 * n) := by
    apply exists_complete_inverse_of_stages p F3 g ε _ _ _
      (33 * ε / γ ^ 3) (9537 * ε / γ ^ 5) hε1 hsym hd hs hg hstep1 hstep2
    · obtain ⟨w, hsw, htw, hew, hbw⟩ := exists_type_correction_F3 p g (ε * n ^ 2)
        (γ * n) (by positivity) hlarge hmin hsym hs hc (classTotal_bound p g ε hε hg)
      exact ⟨w, hsw, htw, hew, fun a b c => he0 ▸ hbw a b c⟩
    · intro d hz hds hdb
      refine ⟨f3VertexWeight p d, f3VertexWeight_symmetric p d,
        f3VertexWeight_supported p d, f3VertexWeight_rows p d hz hds hm, ?_⟩
      intro a b c
      exact he1 ▸ f3VertexWeight_bound p d (n * (33 * ε / γ ^ 3)) (γ * n)
        (by positivity) hlarge hdb hmin a b c
    · intro f hf _hfd hfs hr hb
      refine ⟨f3ZeroRowWeight p f, f3ZeroRowWeight_symmetric p f,
        f3ZeroRowWeight_supported p f, f3ZeroRowWeight_load p f hf hr hfs hm, ?_⟩
      intro a b c
      exact he2 ▸ f3ZeroRowWeight_bound p f (9537 * ε / γ ^ 5) (γ * n)
        hε2 hlarge hb hmin a b c
  obtain ⟨w, hsw, htw, hew, hbw⟩ := hstage
  exact ⟨w, hsw, htw, hew, fun a b c => (hbw a b c).trans hbudget⟩

theorem exists_complete_chain_inverse_F3 (p : V → Fin 4) (r : Sym2 V → ℝ) (ε γ : ℝ)
    (hε : 0 ≤ ε) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hlarge : 4 ≤ γ * (Fintype.card V : ℝ))
    (hmin : ∀ i, γ * (Fintype.card V : ℝ) ≤ classSize p i)
    (hs : Sym2DemandSupported p F3 r) (hr : ∀ e, |r e| ≤ ε)
    (hc : F3RealCompatible p (fun a b => r s(a, b))) :
    ∃ z : TriangleChain V, CopySupported p F3 (activeCompleteGraph p F3) z ∧
      boundary z = r ∧
      ∀ T, |z T| ≤ (2 : ℝ) ^ 20 * ε / (γ ^ 6 * (Fintype.card V : ℝ)) := by
  obtain ⟨w, hsw, htw, hlw, hbw⟩ := exists_complete_inverse_F3 p (fun a b => r s(a, b)) ε γ
    hε hγ hγ1 hlarge hmin (fun a b => congrArg r Sym2.eq_swap) hs.diag hs.edgeSupported
    (fun a b => hr s(a, b)) hc
  obtain ⟨z, hbz, hlz⟩ := exists_copy_weights_of_ternary p F3 w hsw htw _ hbw
  have hlz' : ∀ e : Sym2 V,
      (∑ S ∈ copies p F3 (activeCompleteGraph p F3) with e ∈ triEdges S, z S) = r e := by
    intro e
    induction e using Sym2.ind with
    | _ a b =>
      by_cases hab : a = b
      · subst b
        rw [copy_load_diag, hs.diag]
      · exact (hlz a b hab).trans (hlw a b)
  refine ⟨copyRestriction p F3 (activeCompleteGraph p F3) z,
    copyRestriction_supported p F3 (activeCompleteGraph p F3) z, ?_, ?_⟩
  · funext e
    exact (copyRestriction_boundary p F3 (activeCompleteGraph p F3) z e).trans (hlz' e)
  · intro T
    by_cases hT : IsCopy p F3 (activeCompleteGraph p F3) T
    · simpa only [copyRestriction, hT, ite_true] using hbz T hT
    · simp only [copyRestriction, hT, ite_false, abs_zero]
      positivity

theorem exists_host_chain_inverse_F3 (p : V → Fin 4)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : Sym2 V → ℝ) (ε ω : ℝ) (hε : 0 ≤ ε) (hω : 0 < ω) (hω1 : ω ≤ 1)
    (hlarge : 4 ≤ ω * (Fintype.card V : ℝ))
    (hmin : ∀ i, ω * (Fintype.card V : ℝ) ≤ classSize p i)
    (hguard : GuardedSupply p G (fun i j => ∃ k, Link F3 i j k) 4
      (ω * Fintype.card V / 2))
    (hs : Sym2DemandSupported p F3 r) (hzero : ∀ e, e ∉ G.edgeFinset → r e = 0)
    (hr : ∀ e, |r e| ≤ ε)
    (hc : F3RealCompatible p (fun a b => r s(a, b))) :
    ∃ w : TriangleChain V, CopySupported p F3 G w ∧ boundary w = r ∧
      ∀ T, IsCopy p F3 G T →
        |w T| ≤ ((2 : ℝ) ^ 32 / ω ^ 9) * ε / Fintype.card V := by
  classical
  have hn : 0 < Fintype.card V := by
    by_contra h
    have hz : Fintype.card V = 0 := by omega
    simp only [hz, Nat.cast_zero, mul_zero] at hlarge
    norm_num at hlarge
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast hn
  obtain ⟨z, hzs, hzr, hzb⟩ := exists_complete_chain_inverse_F3 p r ε ω
    hε hω hω1 hlarge hmin hs hr hc
  let M : ℝ := (2 : ℝ) ^ 20 * ε / (ω ^ 6 * Fintype.card V)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hS := total_mass_bound p F3 (activeCompleteGraph p F3) z M hM (fun T _ => hzb T)
  have hU := vertex_mass_bound p F3 (activeCompleteGraph p F3) z M hM (fun T _ => hzb T)
  obtain ⟨w, hws, hwr, hwb⟩ := SignedTransfer.exists_signed_transfer p F3 G
    (ω * Fintype.card V / 2) ε ((Fintype.card V : ℝ) ^ 3 * M)
    ((Fintype.card V : ℝ) ^ 2 * M) (by positivity) hguard z hzs
    (by intro e he; rw [hzr]; exact hzero e he)
    (by intro e; rw [hzr]; exact hr e) hS hU
  refine ⟨w, hws, hwr.trans hzr, ?_⟩
  intro T hT
  exact (hwb T hT.1.card_eq).trans (transferred_inverse_bound ε ω (Fintype.card V)
    hε hω hω1 hnR)

theorem loadDefect_F3 (p : V → Fin 4) (G : SimpleGraph V) [DecidableRel G.Adj]
    (φ : TriangleChain V) (hdiv : IsIntDiv p F3 G.edgeFinset) :
    F3RealCompatible p (fun a b => loadDefect p F3 G φ s(a, b)) := by
  have hloop : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag :=
    fun _ he => G.not_isDiag_of_mem_edgeFinset he
  rw [loadDefect_eq_indicator_sub_boundary]
  exact F3RealCompatible.residual_of_isIntDiv p G.edgeFinset hloop hdiv G
    (copyRestriction p F3 G φ) (copyRestriction_supported p F3 G φ)

#print axioms exists_complete_inverse_F3
#print axioms exists_host_chain_inverse_F3
#print axioms loadDefect_F3

end PaddedF3
