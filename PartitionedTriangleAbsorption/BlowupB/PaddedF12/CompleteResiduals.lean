/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import PartitionedTriangleAbsorption.BlowupB.PaddedF12.TypeInverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.VertexInverse
public import PartitionedTriangleAbsorption.BlowupB.PaddedFractional.ZeroRowInverse

@[expose] public section

/-! # Residual estimates for the complete allowed blowup inverse -/

noncomputable section

namespace PartitionedTriangleAbsorption.BlowupB.PaddedFractional

open Finset TypedTransformer TypedApplicationLinks

variable {V : Type*} [Fintype V] [DecidableEq V]

set_option linter.unusedSectionVars false

theorem classSize_le_card (p : V → Fin 4) (i : Fin 4) :
    classSize p i ≤ (Fintype.card V : ℝ) := by
  unfold classSize
  exact_mod_cast (card_le_card (subset_univ (classVertices p i)))

theorem abs_sum_le_card_bound {ι : Type*} (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ M) : |∑ i ∈ s, f i| ≤ (s.card : ℝ) * M := by
  calc
    _ ≤ ∑ i ∈ s, |f i| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ s, M := sum_le_sum hf
    _ = _ := by simp [nsmul_eq_mul]

theorem classRow_bound (p : V → Fin 4) (g : V → V → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hg : ∀ a b, |g a b| ≤ ε) (a : V) (i : Fin 4) :
    |classRow p g a i| ≤ (Fintype.card V : ℝ) * ε := by
  apply (abs_sum_le_card_bound (classVertices p i) (g a) ε (fun b _ => hg a b)).trans
  exact mul_le_mul_of_nonneg_right (classSize_le_card p i) hε

theorem classTotal_bound (p : V → Fin 4) (g : V → V → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hg : ∀ a b, |g a b| ≤ ε) (i j : Fin 4) :
    |classTotal p g i j| ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  have hc : 0 ≤ (Fintype.card V : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ classSize p i * ((Fintype.card V : ℝ) * ε) :=
      abs_sum_le_card_bound (classVertices p i) (fun a => classRow p g a j) _
        (fun a _ => classRow_bound p g ε hε hg a j)
    _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) * ε) :=
      mul_le_mul_of_nonneg_right (classSize_le_card p i) (mul_nonneg hc hε)
    _ = _ := by ring

theorem ternaryLoad_bound (w : V → V → V → ℝ) (M : ℝ)
    (hw : ∀ a b c, |w a b c| ≤ M) (a b : V) :
    |ternaryLoad w a b| ≤ (Fintype.card V : ℝ) * M := by
  simpa only [card_univ, ternaryLoad] using
    abs_sum_le_card_bound univ (w a b) M (fun c _ => hw a b c)

theorem TernarySymmetric.load_symmetric {w : V → V → V → ℝ}
    (hw : TernarySymmetric w) (a b : V) : ternaryLoad w a b = ternaryLoad w b a := by
  unfold ternaryLoad
  exact sum_congr rfl (fun c _ => hw.1 a b c)

theorem TernarySupported.edgeSupported {p : V → Fin 4}
    {F : Finset (Multiset (Fin 4))} {w : V → V → V → ℝ}
    (hw : TernarySupported p F w) : EdgeSupported p F (ternaryLoad w) := by
  intro a b hab
  unfold ternaryLoad
  apply sum_eq_zero
  intro c _
  exact hw a b c (fun h => hab ⟨p c, h.2.2.2⟩)

theorem EdgeSupported.sub {p : V → Fin 4} {F : Finset (Multiset (Fin 4))}
    {g h : V → V → ℝ} (hg : EdgeSupported p F g) (hh : EdgeSupported p F h) :
    EdgeSupported p F (fun a b => g a b - h a b) := by
  intro a b hab
  dsimp only
  rw [hg a b hab, hh a b hab, sub_self]

theorem EdgeSupported.rows {p : V → Fin 4} {F : Finset (Multiset (Fin 4))}
    {g : V → V → ℝ} (hg : EdgeSupported p F g) :
    VertexDemandSupported p F (classRow p g) := by
  intro a i hi
  unfold classRow
  apply sum_eq_zero
  intro b hb
  apply hg a b
  simpa only [(mem_classVertices p i b).mp hb] using hi

theorem classRow_sub (p : V → Fin 4) (g h : V → V → ℝ) (a : V) (i : Fin 4) :
    classRow p (fun a b => g a b - h a b) a i = classRow p g a i - classRow p h a i := by
  simp only [classRow, sum_sub_distrib]

theorem residual_vertexDemandZero (p : V → Fin 4) (g h : V → V → ℝ)
    (ht : classTotal p h = classTotal p g) :
    VertexDemandZero p (classRow p (fun a b => g a b - h a b)) := by
  intro i j
  change classTotal p (fun a b => g a b - h a b) i j = 0
  rw [classTotal_sub, ht, sub_self]

theorem residual_classRowsZero (p : V → Fin 4) (g h : V → V → ℝ)
    (ht : ∀ a i, classRow p h a i = classRow p g a i) :
    ClassRowsZero p (fun a b => g a b - h a b) := by
  intro a i
  change classRow p (fun a b => g a b - h a b) a i = 0
  rw [classRow_sub, ht, sub_self]

theorem residual_bound (g : V → V → ℝ) (w : V → V → V → ℝ) (ε M : ℝ)
    (hg : ∀ a b, |g a b| ≤ ε) (hw : ∀ a b c, |w a b c| ≤ M) (a b : V) :
    |g a b - ternaryLoad w a b| ≤ ε + (Fintype.card V : ℝ) * M := by
  exact (abs_sub _ _).trans (add_le_add (hg a b) (ternaryLoad_bound w M hw a b))

#print axioms classTotal_bound
#print axioms TernarySupported.edgeSupported
#print axioms residual_vertexDemandZero
#print axioms residual_classRowsZero

end PartitionedTriangleAbsorption.BlowupB.PaddedFractional
